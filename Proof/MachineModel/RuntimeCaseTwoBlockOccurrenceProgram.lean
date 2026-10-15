import Proof.MachineModel.CaseTwoBlockOccurrenceProgram

namespace NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CaseTwoBlockOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceCoordinates
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RuntimeLeftShiftProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The numeral packet and its accessors -/

private theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

private theorem le_pair_of_le_left {value left right : ℕ}
    (hvalue : value ≤ left) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_of_le_right {value left right : ℕ}
    (hvalue : value ≤ right) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-- The seven numerals of the per-block occurrence callee, packed into one
word.  The callee is entered with this word in the input-length register. -/
def occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair arity
      (Nat.pair inputArity (Nat.pair paddedInputBits paddedClauseBits)))
    (Nat.pair nativeClauseBits (Nat.pair circuitSize encoded))

/-- The block arity. -/
def packetArity (packet : ℕ) : ℕ := (Nat.unpair (Nat.unpair packet).1).1

/-- The substituted circuit's arity, the outer native width. -/
def packetInputArity (packet : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair packet).1).2).1

/-- The padded input width. -/
def packetPaddedInputBits (packet : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair packet).1).2).2).1

/-- The padded clause width. -/
def packetPaddedClauseBits (packet : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair packet).1).2).2).2

/-- The factory's own clause width at the substituted circuit. -/
def packetNativeClauseBits (packet : ℕ) : ℕ := (Nat.unpair (Nat.unpair packet).2).1

/-- The substituted circuit's size. -/
def packetCircuitSize (packet : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair packet).2).2).1

/-- The substituted circuit's encoding. -/
def packetEncoded (packet : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair (Nat.unpair packet).2).2).2

@[simp] theorem packetArity_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetArity
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = arity := by
  simp [packetArity, occurrencePacket]

@[simp] theorem packetInputArity_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetInputArity
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = inputArity := by
  simp [packetInputArity, occurrencePacket]

@[simp] theorem packetPaddedInputBits_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetPaddedInputBits
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = paddedInputBits := by
  simp [packetPaddedInputBits, occurrencePacket]

@[simp] theorem packetPaddedClauseBits_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetPaddedClauseBits
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = paddedClauseBits := by
  simp [packetPaddedClauseBits, occurrencePacket]

@[simp] theorem packetNativeClauseBits_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetNativeClauseBits
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = nativeClauseBits := by
  simp [packetNativeClauseBits, occurrencePacket]

@[simp] theorem packetCircuitSize_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetCircuitSize
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = circuitSize := by
  simp [packetCircuitSize, occurrencePacket]

@[simp] theorem packetEncoded_occurrencePacket
    (arity inputArity paddedInputBits paddedClauseBits nativeClauseBits
      circuitSize encoded : ℕ) :
    packetEncoded
        (occurrencePacket arity inputArity paddedInputBits paddedClauseBits
          nativeClauseBits circuitSize encoded) = encoded := by
  simp [packetEncoded, occurrencePacket]

theorem packetArity_le (packet : ℕ) : packetArity packet ≤ packet :=
  (Nat.unpair_left_le _).trans (Nat.unpair_left_le _)

theorem packetInputArity_le (packet : ℕ) : packetInputArity packet ≤ packet :=
  (Nat.unpair_left_le _).trans
    ((Nat.unpair_right_le _).trans (Nat.unpair_left_le _))

theorem packetPaddedInputBits_le (packet : ℕ) :
    packetPaddedInputBits packet ≤ packet :=
  (Nat.unpair_left_le _).trans
    ((Nat.unpair_right_le _).trans
      ((Nat.unpair_right_le _).trans (Nat.unpair_left_le _)))

theorem packetPaddedClauseBits_le (packet : ℕ) :
    packetPaddedClauseBits packet ≤ packet :=
  (Nat.unpair_right_le _).trans
    ((Nat.unpair_right_le _).trans
      ((Nat.unpair_right_le _).trans (Nat.unpair_left_le _)))

theorem packetNativeClauseBits_le (packet : ℕ) :
    packetNativeClauseBits packet ≤ packet :=
  (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)

theorem packetCircuitSize_le (packet : ℕ) : packetCircuitSize packet ≤ packet :=
  (Nat.unpair_left_le _).trans
    ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

theorem packetEncoded_le (packet : ℕ) : packetEncoded packet ≤ packet :=
  (Nat.unpair_right_le _).trans
    ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _))

/-! ## 2. The block window of the requested point code

Register ABI as in the frozen adapters, with `r15` the packet cursor: `r2` the
leading field of the request, `r3` its trailing field, `r4` the block arity read
from the packet, `r5` the assembled callee request. -/

/-- Frame the requested `pair block pointCode` as the bit-serial product
request for the block's digit offset, with the block arity read from the
packet. -/
def runtimeBlockOffsetPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 1 15 3
  , .unpairLeft 15 4 4
  , .pair 2 4 5 5
  , .pair 5 3 0 6
  , .halt 0
  ]

@[simp] theorem runtimeBlockOffsetPrepProgram_oracleFree :
    OracleFree runtimeBlockOffsetPrepProgram := by
  rfl

def runtimeBlockOffsetPrepBits (packet block pointCode : ℕ) : ℕ :=
  natBitLength
    (max packet
      (max (Nat.pair block pointCode)
        (blockOffsetPrepOutput (packetArity packet) block pointCode)))

theorem run_runtimeBlockOffsetPrepProgram (packet block pointCode : ℕ) :
    runNPOracleProgram runtimeBlockOffsetPrepProgram
        (runtimeBlockOffsetPrepBits packet block pointCode) 7
        (initialNPOracleState packet (Nat.pair block pointCode)) =
      some (blockOffsetPrepOutput (packetArity packet) block pointCode) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤ runtimeBlockOffsetPrepBits packet block pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair block pointCode →
      natBitLength value ≤ runtimeBlockOffsetPrepBits packet block pointCode :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤ blockOffsetPrepOutput (packetArity packet) block pointCode →
      natBitLength value ≤ runtimeBlockOffsetPrepBits packet block pointCode :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hblock := hrequest block (Nat.left_le_pair block pointCode)
  have hpoint := hrequest pointCode (Nat.right_le_pair block pointCode)
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have harity := hpacket _ (packetArity_le packet)
  have hproduct :=
    hresult (bitSerialMulInput block (packetArity packet))
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := block) (by rfl) rfl
    (by simp [initialNPOracleState]) hblock]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpoint]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetArity packet) (by rfl) rfl
    (by simp [packetArity, NPOracleState.write, NPOracleState.jump]) harity]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSerialMulInput block (packetArity packet)) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSerialMulInput])
    hproduct]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := blockOffsetPrepOutput (packetArity packet) block pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, blockOffsetPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Frame the computed digit offset and the retained point code as the digit
window request of the block, with the block arity read from the packet. -/
def runtimeBlockWindowPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 1 15 3
  , .unpairLeft 15 4 4
  , .pair 4 3 5 5
  , .pair 2 5 0 6
  , .halt 0
  ]

@[simp] theorem runtimeBlockWindowPrepProgram_oracleFree :
    OracleFree runtimeBlockWindowPrepProgram := by
  rfl

def runtimeBlockWindowPrepBits (packet offset pointCode : ℕ) : ℕ :=
  natBitLength
    (max packet
      (max (Nat.pair offset pointCode)
        (bitSliceInput offset (packetArity packet) pointCode)))

theorem run_runtimeBlockWindowPrepProgram (packet offset pointCode : ℕ) :
    runNPOracleProgram runtimeBlockWindowPrepProgram
        (runtimeBlockWindowPrepBits packet offset pointCode) 7
        (initialNPOracleState packet (Nat.pair offset pointCode)) =
      some (bitSliceInput offset (packetArity packet) pointCode) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤ runtimeBlockWindowPrepBits packet offset pointCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair offset pointCode →
      natBitLength value ≤ runtimeBlockWindowPrepBits packet offset pointCode :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤ bitSliceInput offset (packetArity packet) pointCode →
      natBitLength value ≤ runtimeBlockWindowPrepBits packet offset pointCode :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hoffset := hrequest offset (Nat.left_le_pair offset pointCode)
  have hpoint := hrequest pointCode (Nat.right_le_pair offset pointCode)
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have harity := hpacket _ (packetArity_le packet)
  have htail :=
    hresult (Nat.pair (packetArity packet) pointCode)
      (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := offset) (by rfl) rfl
    (by simp [initialNPOracleState]) hoffset]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := pointCode) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hpoint]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetArity packet) (by rfl) rfl
    (by simp [packetArity, NPOracleState.write, NPOracleState.jump]) harity]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (packetArity packet) pointCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSliceInput offset (packetArity packet) pointCode) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 3. The native occurrence code of one block window

The four adapters of the occurrence-code assembly, each reading its own
numerals from the packet.  Register `r15` is the packet cursor throughout and
`r16`/`r17` hold the two summands of a width that the frozen adapters carried
as a single immediate. -/

/-- The low input window and the position digit, with the padded widths and
the circuit arity read from the packet. -/
def runtimeBlockDigitPrepProgram : NPOracleProgram :=
  [ .unpairLeft 1 15 1
  , .unpairRight 15 15 2
  , .unpairRight 15 15 3
  , .unpairLeft 15 16 4
  , .unpairRight 15 17 5
  , .add 16 17 2 6
  , .testBit 0 2 3 7
  , .pair 3 0 4 8
  , .set 5 0 9
  , .unpairLeft 1 15 10
  , .unpairRight 15 15 11
  , .unpairLeft 15 6 12
  , .pair 6 0 7 13
  , .pair 5 7 8 14
  , .pair 8 4 0 15
  , .halt 0
  ]

@[simp] theorem runtimeBlockDigitPrepProgram_oracleFree :
    OracleFree runtimeBlockDigitPrepProgram := by
  rfl

def runtimeBlockDigitPrepBits (packet window : ℕ) : ℕ :=
  natBitLength
    (max packet
      (max (packetPaddedInputBits packet + packetPaddedClauseBits packet)
        (max window
          (blockDigitPrepOutput (packetInputArity packet)
            (packetPaddedInputBits packet) (packetPaddedClauseBits packet)
            window))))

theorem run_runtimeBlockDigitPrepProgram (packet window : ℕ) :
    runNPOracleProgram runtimeBlockDigitPrepProgram
        (runtimeBlockDigitPrepBits packet window) 16
        (initialNPOracleState packet window) =
      some
        (blockDigitPrepOutput (packetInputArity packet)
          (packetPaddedInputBits packet) (packetPaddedClauseBits packet)
          window) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤ runtimeBlockDigitPrepBits packet window :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hindex :
      natBitLength
          (packetPaddedInputBits packet + packetPaddedClauseBits packet) ≤
        runtimeBlockDigitPrepBits packet window :=
    natBitLength_mono ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hwindow : natBitLength window ≤ runtimeBlockDigitPrepBits packet window :=
    natBitLength_mono
      ((Nat.le_max_left _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤
        blockDigitPrepOutput (packetInputArity packet)
          (packetPaddedInputBits packet) (packetPaddedClauseBits packet)
          window →
      natBitLength value ≤ runtimeBlockDigitPrepBits packet window :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans
          ((Nat.le_max_right _ _).trans
            ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have hheadTail :=
    hpacket _ ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet))
  have hwidths :=
    hpacket _
      ((Nat.unpair_right_le _).trans
        ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet)))
  have hpadded := hpacket _ (packetPaddedInputBits_le packet)
  have hclause := hpacket _ (packetPaddedClauseBits_le packet)
  have harity := hpacket _ (packetInputArity_le packet)
  have hdigit :=
    hresult
      (window.testBit
          (packetPaddedInputBits packet + packetPaddedClauseBits packet)).toNat
      (le_pair_of_le_right (Nat.left_le_pair _ _))
  have hcontext :=
    hresult
      (Nat.pair
        (window.testBit
            (packetPaddedInputBits packet +
              packetPaddedClauseBits packet)).toNat window)
      (le_pair_of_le_right (le_refl _))
  have hzero := hresult 0 (Nat.zero_le _)
  have htail :=
    hresult (Nat.pair (packetInputArity packet) window)
      (le_pair_of_le_left
        (Nat.right_le_pair 0 (Nat.pair (packetInputArity packet) window)))
  have hslice :=
    hresult (bitSliceInput 0 (packetInputArity packet) window)
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState]) hhead]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadTail]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair (Nat.unpair packet).1).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidths]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetPaddedInputBits packet)
    (by rfl) rfl
    (by simp [packetPaddedInputBits, NPOracleState.write, NPOracleState.jump])
    hpadded]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := packetPaddedClauseBits packet)
    (by rfl) rfl
    (by simp [packetPaddedClauseBits, NPOracleState.write, NPOracleState.jump])
    hclause]
  rw [show 11 = 10 + 1 by omega]
  rw [run_add_instruction
    (value := packetPaddedInputBits packet + packetPaddedClauseBits packet)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindex]
  rw [show 10 = 9 + 1 by omega]
  rw [run_testBit_instruction
    (value :=
      (window.testBit
          (packetPaddedInputBits packet +
            packetPaddedClauseBits packet)).toNat)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hdigit]
  rw [show 9 = 8 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (window.testBit
            (packetPaddedInputBits packet +
              packetPaddedClauseBits packet)).toNat window)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 8 = 7 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadTail]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetInputArity packet) (by rfl) rfl
    (by simp [packetInputArity, NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (packetInputArity packet) window)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSliceInput 0 (packetInputArity packet) window) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput]) hslice]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockDigitPrepOutput (packetInputArity packet)
        (packetPaddedInputBits packet) (packetPaddedClauseBits packet) window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, blockDigitPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The interior clause window, with the factory clause width and the padded
input width read from the packet. -/
def runtimeBlockClausePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .pair 2 4 6 5
  , .unpairRight 1 15 6
  , .unpairLeft 15 7 7
  , .pair 7 5 8 8
  , .unpairLeft 1 15 9
  , .unpairRight 15 15 10
  , .unpairRight 15 15 11
  , .unpairLeft 15 9 12
  , .pair 9 8 10 13
  , .pair 10 6 0 14
  , .halt 0
  ]

@[simp] theorem runtimeBlockClausePrepProgram_oracleFree :
    OracleFree runtimeBlockClausePrepProgram := by
  rfl

def runtimeBlockClausePrepBits (packet low digit window : ℕ) : ℕ :=
  natBitLength
    (max packet
      (max (Nat.pair low (Nat.pair digit window))
        (blockClausePrepOutput (packetPaddedInputBits packet)
          (packetNativeClauseBits packet) low digit window)))

theorem run_runtimeBlockClausePrepProgram (packet low digit window : ℕ) :
    runNPOracleProgram runtimeBlockClausePrepProgram
        (runtimeBlockClausePrepBits packet low digit window) 15
        (initialNPOracleState packet (Nat.pair low (Nat.pair digit window))) =
      some
        (blockClausePrepOutput (packetPaddedInputBits packet)
          (packetNativeClauseBits packet) low digit window) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤ runtimeBlockClausePrepBits packet low digit window :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair low (Nat.pair digit window) →
      natBitLength value ≤ runtimeBlockClausePrepBits packet low digit window :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤
        blockClausePrepOutput (packetPaddedInputBits packet)
          (packetNativeClauseBits packet) low digit window →
      natBitLength value ≤ runtimeBlockClausePrepBits packet low digit window :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hlow := hrequest low (Nat.left_le_pair _ _)
  have hcontext := hrequest (Nat.pair digit window) (Nat.right_le_pair _ _)
  have hdigit :=
    hrequest digit (le_pair_of_le_right (Nat.left_le_pair digit window))
  have hwindow :=
    hrequest window (le_pair_of_le_right (Nat.right_le_pair digit window))
  have hpair := hresult (Nat.pair low digit) (Nat.right_le_pair _ _)
  have htailWord := hpacket _ (Nat.unpair_right_le packet)
  have hnative := hpacket _ (packetNativeClauseBits_le packet)
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have hheadTail :=
    hpacket _ ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet))
  have hwidths :=
    hpacket _
      ((Nat.unpair_right_le _).trans
        ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet)))
  have hpadded := hpacket _ (packetPaddedInputBits_le packet)
  have hslicetail :=
    hresult (Nat.pair (packetNativeClauseBits packet) window)
      (le_pair_of_le_left (Nat.right_le_pair _ _))
  have hslice :=
    hresult
      (bitSliceInput (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairLeft_instruction (value := low) (by rfl) rfl
    (by simp [initialNPOracleState]) hlow]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair digit window) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := digit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdigit]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := window) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwindow]
  rw [show 11 = 10 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair low digit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hpair]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair packet).2) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailWord]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetNativeClauseBits packet)
    (by rfl) rfl
    (by simp [packetNativeClauseBits, NPOracleState.write, NPOracleState.jump])
    hnative]
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (packetNativeClauseBits packet) window) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hslicetail]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadTail]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair (Nat.unpair packet).1).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidths]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetPaddedInputBits packet)
    (by rfl) rfl
    (by simp [packetPaddedInputBits, NPOracleState.write, NPOracleState.jump])
    hpadded]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      bitSliceInput (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput]) hslice]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockClausePrepOutput (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) low digit window)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, blockClausePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The clause window's scaling exponent, read from the packet. -/
def runtimeBlockClauseShiftPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 1 15 3
  , .unpairRight 15 15 4
  , .unpairLeft 15 4 5
  , .pair 4 2 5 6
  , .pair 5 3 0 7
  , .halt 0
  ]

@[simp] theorem runtimeBlockClauseShiftPrepProgram_oracleFree :
    OracleFree runtimeBlockClauseShiftPrepProgram := by
  rfl

def runtimeBlockClauseShiftPrepBits (packet clause low digit : ℕ) : ℕ :=
  natBitLength
    (max packet
      (max (Nat.pair clause (Nat.pair low digit))
        (blockClauseShiftPrepOutput (packetInputArity packet) clause low
          digit)))

theorem run_runtimeBlockClauseShiftPrepProgram (packet clause low digit : ℕ) :
    runNPOracleProgram runtimeBlockClauseShiftPrepProgram
        (runtimeBlockClauseShiftPrepBits packet clause low digit) 8
        (initialNPOracleState packet (Nat.pair clause (Nat.pair low digit))) =
      some
        (blockClauseShiftPrepOutput (packetInputArity packet) clause low
          digit) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤
        runtimeBlockClauseShiftPrepBits packet clause low digit :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair clause (Nat.pair low digit) →
      natBitLength value ≤
        runtimeBlockClauseShiftPrepBits packet clause low digit :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤
        blockClauseShiftPrepOutput (packetInputArity packet) clause low digit →
      natBitLength value ≤
        runtimeBlockClauseShiftPrepBits packet clause low digit :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hclause := hrequest clause (Nat.left_le_pair _ _)
  have hcontext := hrequest (Nat.pair low digit) (Nat.right_le_pair _ _)
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have hheadTail :=
    hpacket _ ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet))
  have harity := hpacket _ (packetInputArity_le packet)
  have hshift :=
    hresult (runtimeLeftShiftInput (packetInputArity packet) clause)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := clause) (by rfl) rfl
    (by simp [initialNPOracleState]) hclause]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair low digit) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadTail]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetInputArity packet) (by rfl) rfl
    (by simp [packetInputArity, NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := runtimeLeftShiftInput (packetInputArity packet) clause)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, runtimeLeftShiftInput])
    hshift]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockClauseShiftPrepOutput (packetInputArity packet) clause low digit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      blockClauseShiftPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The position digit's scaling exponent, assembled at run time from the two
packet fields the frozen adapter added off line. -/
def runtimeBlockDigitShiftPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .add 4 2 6 5
  , .unpairLeft 1 15 6
  , .unpairRight 15 15 7
  , .unpairLeft 15 16 8
  , .unpairRight 1 15 9
  , .unpairLeft 15 17 10
  , .add 16 17 7 11
  , .pair 7 5 8 12
  , .pair 8 6 0 13
  , .halt 0
  ]

@[simp] theorem runtimeBlockDigitShiftPrepProgram_oracleFree :
    OracleFree runtimeBlockDigitShiftPrepProgram := by
  rfl

def runtimeBlockDigitShiftPrepBits (packet scaledClause low digit : ℕ) : ℕ :=
  natBitLength
    (max packet
      (max (Nat.pair scaledClause (Nat.pair low digit))
        (blockDigitShiftPrepOutput (packetInputArity packet)
          (packetNativeClauseBits packet) scaledClause low digit)))

theorem run_runtimeBlockDigitShiftPrepProgram
    (packet scaledClause low digit : ℕ) :
    runNPOracleProgram runtimeBlockDigitShiftPrepProgram
        (runtimeBlockDigitShiftPrepBits packet scaledClause low digit) 14
        (initialNPOracleState packet
          (Nat.pair scaledClause (Nat.pair low digit))) =
      some
        (blockDigitShiftPrepOutput (packetInputArity packet)
          (packetNativeClauseBits packet) scaledClause low digit) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤
        runtimeBlockDigitShiftPrepBits packet scaledClause low digit :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hrequest : ∀ value : ℕ,
      value ≤ Nat.pair scaledClause (Nat.pair low digit) →
      natBitLength value ≤
        runtimeBlockDigitShiftPrepBits packet scaledClause low digit :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hresult : ∀ value : ℕ,
      value ≤
        blockDigitShiftPrepOutput (packetInputArity packet)
          (packetNativeClauseBits packet) scaledClause low digit →
      natBitLength value ≤
        runtimeBlockDigitShiftPrepBits packet scaledClause low digit :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hscaled := hrequest scaledClause (Nat.left_le_pair _ _)
  have hcontext := hrequest (Nat.pair low digit) (Nat.right_le_pair _ _)
  have hlow := hrequest low (le_pair_of_le_right (Nat.left_le_pair low digit))
  have hdigit :=
    hrequest digit (le_pair_of_le_right (Nat.right_le_pair low digit))
  have hsum := hresult (low + scaledClause) (Nat.right_le_pair _ _)
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have hheadTail :=
    hpacket _ ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet))
  have harity := hpacket _ (packetInputArity_le packet)
  have htailWord := hpacket _ (Nat.unpair_right_le packet)
  have hnative := hpacket _ (packetNativeClauseBits_le packet)
  have hexponent :=
    hresult (packetInputArity packet + packetNativeClauseBits packet)
      (le_pair_of_le_left (Nat.left_le_pair _ digit))
  have hshift :=
    hresult
      (runtimeLeftShiftInput
        (packetInputArity packet + packetNativeClauseBits packet) digit)
      (Nat.left_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := scaledClause) (by rfl) rfl
    (by simp [initialNPOracleState]) hscaled]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair low digit) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := low) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlow]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := digit) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdigit]
  rw [show 10 = 9 + 1 by omega]
  rw [run_add_instruction (value := low + scaledClause) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsum]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadTail]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetInputArity packet) (by rfl) rfl
    (by simp [packetInputArity, NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair packet).2) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailWord]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetNativeClauseBits packet)
    (by rfl) rfl
    (by simp [packetNativeClauseBits, NPOracleState.write, NPOracleState.jump])
    hnative]
  rw [show 4 = 3 + 1 by omega]
  rw [run_add_instruction
    (value := packetInputArity packet + packetNativeClauseBits packet)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hexponent]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      runtimeLeftShiftInput
        (packetInputArity packet + packetNativeClauseBits packet) digit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, runtimeLeftShiftInput])
    hshift]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      blockDigitShiftPrepOutput (packetInputArity packet)
        (packetNativeClauseBits packet) scaledClause low digit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      blockDigitShiftPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 4. The occurrence call frame -/

/-- The published occurrence ABI, with the circuit's arity, size and encoding
read from the packet. -/
def runtimeBlockOccurrenceFramePrepProgram : NPOracleProgram :=
  [ .unpairRight 1 15 1
  , .unpairRight 15 15 2
  , .unpairRight 15 2 3
  , .pair 2 0 3 4
  , .unpairRight 1 15 5
  , .unpairRight 15 15 6
  , .unpairLeft 15 4 7
  , .pair 4 3 5 8
  , .unpairLeft 1 15 9
  , .unpairRight 15 15 10
  , .unpairLeft 15 6 11
  , .pair 6 5 0 12
  , .halt 0
  ]

@[simp] theorem runtimeBlockOccurrenceFramePrepProgram_oracleFree :
    OracleFree runtimeBlockOccurrenceFramePrepProgram := by
  rfl

def runtimeBlockOccurrenceFramePrepBits (packet code : ℕ) : ℕ :=
  natBitLength
    (max packet
      (caseTwoOccurrenceInput (packetInputArity packet)
        (packetCircuitSize packet) (packetEncoded packet) code))

theorem run_runtimeBlockOccurrenceFramePrepProgram (packet code : ℕ) :
    runNPOracleProgram runtimeBlockOccurrenceFramePrepProgram
        (runtimeBlockOccurrenceFramePrepBits packet code) 13
        (initialNPOracleState packet code) =
      some
        (caseTwoOccurrenceInput (packetInputArity packet)
          (packetCircuitSize packet) (packetEncoded packet) code) := by
  have hpacket : ∀ value : ℕ, value ≤ packet →
      natBitLength value ≤ runtimeBlockOccurrenceFramePrepBits packet code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        caseTwoOccurrenceInput (packetInputArity packet)
          (packetCircuitSize packet) (packetEncoded packet) code →
      natBitLength value ≤ runtimeBlockOccurrenceFramePrepBits packet code :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have htailWord := hpacket _ (Nat.unpair_right_le packet)
  have hcircuitWord :=
    hpacket _ ((Nat.unpair_right_le _).trans (Nat.unpair_right_le packet))
  have hencoded := hpacket _ (packetEncoded_le packet)
  have hsize := hpacket _ (packetCircuitSize_le packet)
  have hhead := hpacket _ (Nat.unpair_left_le packet)
  have hheadTail :=
    hpacket _ ((Nat.unpair_right_le _).trans (Nat.unpair_left_le packet))
  have harity := hpacket _ (packetInputArity_le packet)
  have hcode :=
    hresult (Nat.pair (packetEncoded packet) code)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have htail :=
    hresult
      (Nat.pair (packetCircuitSize packet)
        (Nat.pair (packetEncoded packet) code))
      (Nat.right_le_pair _ _)
  have houtput := hresult _ (le_refl _)
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair packet).2) (by rfl) rfl
    (by simp [initialNPOracleState]) htailWord]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcircuitWord]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := packetEncoded packet) (by rfl) rfl
    (by simp [packetEncoded, NPOracleState.write, NPOracleState.jump]) hencoded]
  rw [show 10 = 9 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (packetEncoded packet) code)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcode]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair packet).2) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    htailWord]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).2).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcircuitWord]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetCircuitSize packet) (by rfl) rfl
    (by simp [packetCircuitSize, NPOracleState.write, NPOracleState.jump])
    hsize]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (packetCircuitSize packet)
        (Nat.pair (packetEncoded packet) code))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htail]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair packet).1) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hhead]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := (Nat.unpair (Nat.unpair packet).1).2) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hheadTail]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packetInputArity packet) (by rfl) rfl
    (by simp [packetInputArity, NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      caseTwoOccurrenceInput (packetInputArity packet)
        (packetCircuitSize packet) (packetEncoded packet) code)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, caseTwoOccurrenceInput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-! ## 5. The stages, unchanged except for their prologues -/

private def runtimeBlockWindowTailTwo : NPOracleProgram :=
  linkPrograms runtimeBlockWindowPrepProgram bitSliceProgram

private def runtimeBlockWindowTailOne : NPOracleProgram :=
  linkPrograms (preserveRightProgram bitSerialMulProgram)
    runtimeBlockWindowTailTwo

/-- **The block window stage.**  One fixed oracle-free program turning the
requested `pair block pointCode` into the arity-wide digit window of the point
code at that block's offset, with the arity read from the packet. -/
def runtimeBlockWindowProgram : NPOracleProgram :=
  linkPrograms runtimeBlockOffsetPrepProgram runtimeBlockWindowTailOne

theorem runtimeBlockWindowProgram_oracleFree :
    OracleFree runtimeBlockWindowProgram := by
  apply oracleFree_linkPrograms runtimeBlockOffsetPrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree bitSerialMulProgram
      bitSerialMulProgram_oracleFree
  exact oracleFree_linkPrograms runtimeBlockWindowPrepProgram_oracleFree
    bitSliceProgram_oracleFree

def runtimeBlockWindowFuel (packet : ℕ) : ℕ :=
  linkFuel runtimeBlockWindowTailOne 7 <|
    linkFuel runtimeBlockWindowTailTwo
      (preserveRightFuel (bitSerialMulFuel (packetArity packet))) <|
      linkFuel bitSliceProgram 7 (bitSliceFuel (packetArity packet))

def runtimeBlockWindowBits (packet block pointCode : ℕ) : ℕ :=
  occurrenceStageBits packet
    (runtimeBlockOffsetPrepBits packet block pointCode) <|
    occurrenceStageBits packet
      (preserveRightBits (bitSerialMulBits packet block (packetArity packet))
        (bitSerialMulInput block (packetArity packet)) pointCode
        (block * packetArity packet)) <|
      occurrenceStageBits packet
        (runtimeBlockWindowPrepBits packet (block * packetArity packet)
          pointCode)
        (bitSliceBits packet (block * packetArity packet) (packetArity packet)
          pointCode)

theorem run_runtimeBlockWindowProgram (packet block pointCode : ℕ) :
    runNPOracleProgram runtimeBlockWindowProgram
        (runtimeBlockWindowBits packet block pointCode)
        (runtimeBlockWindowFuel packet)
        (initialNPOracleState packet (Nat.pair block pointCode)) =
      some
        (bitSlice (block * packetArity packet) (packetArity packet)
          pointCode) := by
  have hproduct :
      runNPOracleProgram (preserveRightProgram bitSerialMulProgram)
          (preserveRightBits (bitSerialMulBits packet block (packetArity packet))
            (bitSerialMulInput block (packetArity packet)) pointCode
            (block * packetArity packet))
          (preserveRightFuel (bitSerialMulFuel (packetArity packet)))
          (initialNPOracleState packet
            (blockOffsetPrepOutput (packetArity packet) block pointCode)) =
        some (Nat.pair (block * packetArity packet) pointCode) :=
    run_preserveRightProgram bitSerialMulProgram packet
      (bitSerialMulBits packet block (packetArity packet))
      (bitSerialMulFuel (packetArity packet))
      (bitSerialMulInput block (packetArity packet)) pointCode
      (block * packetArity packet)
      (run_bitSerialMulProgram packet block (packetArity packet))
  exact run_occurrenceStage
    (run_runtimeBlockOffsetPrepProgram packet block pointCode)
    (run_occurrenceStage hproduct
      (run_occurrenceStage
        (run_runtimeBlockWindowPrepProgram packet (block * packetArity packet)
          pointCode)
        (run_bitSliceProgram packet (block * packetArity packet)
          (packetArity packet) pointCode)))

/-- The low input window and the position digit, computed. -/
def runtimeBlockLowStageProgram : NPOracleProgram :=
  linkPrograms runtimeBlockDigitPrepProgram
    (preserveRightProgram bitSliceProgram)

theorem runtimeBlockLowStageProgram_oracleFree :
    OracleFree runtimeBlockLowStageProgram :=
  oracleFree_linkPrograms runtimeBlockDigitPrepProgram_oracleFree
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)

def runtimeBlockLowStageFuel (packet : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitSliceProgram) 16
    (preserveRightFuel (bitSliceFuel (packetInputArity packet)))

def runtimeBlockLowStageBits (packet window : ℕ) : ℕ :=
  occurrenceStageBits packet (runtimeBlockDigitPrepBits packet window)
    (preserveRightBits
      (bitSliceBits packet 0 (packetInputArity packet) window)
      (bitSliceInput 0 (packetInputArity packet) window)
      (Nat.pair
        (window.testBit
            (packetPaddedInputBits packet +
              packetPaddedClauseBits packet)).toNat window)
      (bitSlice 0 (packetInputArity packet) window))

theorem run_runtimeBlockLowStageProgram (packet window : ℕ) :
    runNPOracleProgram runtimeBlockLowStageProgram
        (runtimeBlockLowStageBits packet window)
        (runtimeBlockLowStageFuel packet)
        (initialNPOracleState packet window) =
      some
        (Nat.pair (bitSlice 0 (packetInputArity packet) window)
          (Nat.pair
            (window.testBit
                (packetPaddedInputBits packet +
                  packetPaddedClauseBits packet)).toNat window)) :=
  run_occurrenceStage (run_runtimeBlockDigitPrepProgram packet window)
    (run_preserveRightProgram bitSliceProgram packet
      (bitSliceBits packet 0 (packetInputArity packet) window)
      (bitSliceFuel (packetInputArity packet))
      (bitSliceInput 0 (packetInputArity packet) window)
      (Nat.pair
        (window.testBit
            (packetPaddedInputBits packet +
              packetPaddedClauseBits packet)).toNat window)
      (bitSlice 0 (packetInputArity packet) window)
      (run_bitSliceProgram packet 0 (packetInputArity packet) window))

/-- The interior clause window, computed. -/
def runtimeBlockClauseStageProgram : NPOracleProgram :=
  linkPrograms runtimeBlockClausePrepProgram
    (preserveRightProgram bitSliceProgram)

theorem runtimeBlockClauseStageProgram_oracleFree :
    OracleFree runtimeBlockClauseStageProgram :=
  oracleFree_linkPrograms runtimeBlockClausePrepProgram_oracleFree
    (preserveRightProgram_oracleFree bitSliceProgram bitSliceProgram_oracleFree)

def runtimeBlockClauseStageFuel (packet : ℕ) : ℕ :=
  linkFuel (preserveRightProgram bitSliceProgram) 15
    (preserveRightFuel (bitSliceFuel (packetNativeClauseBits packet)))

def runtimeBlockClauseStageBits (packet low digit window : ℕ) : ℕ :=
  occurrenceStageBits packet
    (runtimeBlockClausePrepBits packet low digit window)
    (preserveRightBits
      (bitSliceBits packet (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
      (bitSliceInput (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
      (Nat.pair low digit)
      (bitSlice (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window))

theorem run_runtimeBlockClauseStageProgram (packet low digit window : ℕ) :
    runNPOracleProgram runtimeBlockClauseStageProgram
        (runtimeBlockClauseStageBits packet low digit window)
        (runtimeBlockClauseStageFuel packet)
        (initialNPOracleState packet (Nat.pair low (Nat.pair digit window))) =
      some
        (Nat.pair
          (bitSlice (packetPaddedInputBits packet)
            (packetNativeClauseBits packet) window)
          (Nat.pair low digit)) :=
  run_occurrenceStage
    (run_runtimeBlockClausePrepProgram packet low digit window)
    (run_preserveRightProgram bitSliceProgram packet
      (bitSliceBits packet (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
      (bitSliceFuel (packetNativeClauseBits packet))
      (bitSliceInput (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
      (Nat.pair low digit)
      (bitSlice (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window)
      (run_bitSliceProgram packet (packetPaddedInputBits packet)
        (packetNativeClauseBits packet) window))

/-- The clause window scaled to its place in the occurrence code. -/
def runtimeBlockClauseShiftStageProgram : NPOracleProgram :=
  linkPrograms runtimeBlockClauseShiftPrepProgram
    (preserveRightProgram runtimeLeftShiftProgram)

theorem runtimeBlockClauseShiftStageProgram_oracleFree :
    OracleFree runtimeBlockClauseShiftStageProgram :=
  oracleFree_linkPrograms runtimeBlockClauseShiftPrepProgram_oracleFree
    (preserveRightProgram_oracleFree runtimeLeftShiftProgram
      runtimeLeftShiftProgram_oracleFree)

def runtimeBlockClauseShiftStageFuel (packet clause : ℕ) : ℕ :=
  linkFuel (preserveRightProgram runtimeLeftShiftProgram) 8
    (preserveRightFuel
      (runtimeLeftShiftFuel (packetInputArity packet) clause))

def runtimeBlockClauseShiftStageBits (packet clause low digit : ℕ) : ℕ :=
  occurrenceStageBits packet
    (runtimeBlockClauseShiftPrepBits packet clause low digit)
    (preserveRightBits
      (runtimeLeftShiftBits packet (packetInputArity packet) clause)
      (runtimeLeftShiftInput (packetInputArity packet) clause)
      (Nat.pair low digit) (2 ^ packetInputArity packet * clause))

theorem run_runtimeBlockClauseShiftStageProgram
    (packet clause low digit : ℕ) :
    runNPOracleProgram runtimeBlockClauseShiftStageProgram
        (runtimeBlockClauseShiftStageBits packet clause low digit)
        (runtimeBlockClauseShiftStageFuel packet clause)
        (initialNPOracleState packet (Nat.pair clause (Nat.pair low digit))) =
      some
        (Nat.pair (2 ^ packetInputArity packet * clause)
          (Nat.pair low digit)) :=
  run_occurrenceStage
    (run_runtimeBlockClauseShiftPrepProgram packet clause low digit)
    (run_preserveRightProgram runtimeLeftShiftProgram packet
      (runtimeLeftShiftBits packet (packetInputArity packet) clause)
      (runtimeLeftShiftFuel (packetInputArity packet) clause)
      (runtimeLeftShiftInput (packetInputArity packet) clause)
      (Nat.pair low digit) (2 ^ packetInputArity packet * clause)
      (run_runtimeLeftShiftProgram packet (packetInputArity packet) clause))

/-- The position digit scaled to its place, with the low two summands already
added. -/
def runtimeBlockDigitShiftStageProgram : NPOracleProgram :=
  linkPrograms runtimeBlockDigitShiftPrepProgram
    (preserveRightProgram runtimeLeftShiftProgram)

theorem runtimeBlockDigitShiftStageProgram_oracleFree :
    OracleFree runtimeBlockDigitShiftStageProgram :=
  oracleFree_linkPrograms runtimeBlockDigitShiftPrepProgram_oracleFree
    (preserveRightProgram_oracleFree runtimeLeftShiftProgram
      runtimeLeftShiftProgram_oracleFree)

def runtimeBlockDigitShiftStageFuel (packet digit : ℕ) : ℕ :=
  linkFuel (preserveRightProgram runtimeLeftShiftProgram) 14
    (preserveRightFuel
      (runtimeLeftShiftFuel
        (packetInputArity packet + packetNativeClauseBits packet) digit))

def runtimeBlockDigitShiftStageBits
    (packet scaledClause low digit : ℕ) : ℕ :=
  occurrenceStageBits packet
    (runtimeBlockDigitShiftPrepBits packet scaledClause low digit)
    (preserveRightBits
      (runtimeLeftShiftBits packet
        (packetInputArity packet + packetNativeClauseBits packet) digit)
      (runtimeLeftShiftInput
        (packetInputArity packet + packetNativeClauseBits packet) digit)
      (low + scaledClause)
      (2 ^ (packetInputArity packet + packetNativeClauseBits packet) * digit))

theorem run_runtimeBlockDigitShiftStageProgram
    (packet scaledClause low digit : ℕ) :
    runNPOracleProgram runtimeBlockDigitShiftStageProgram
        (runtimeBlockDigitShiftStageBits packet scaledClause low digit)
        (runtimeBlockDigitShiftStageFuel packet digit)
        (initialNPOracleState packet
          (Nat.pair scaledClause (Nat.pair low digit))) =
      some
        (Nat.pair
          (2 ^ (packetInputArity packet + packetNativeClauseBits packet) *
            digit)
          (low + scaledClause)) :=
  run_occurrenceStage
    (run_runtimeBlockDigitShiftPrepProgram packet scaledClause low digit)
    (run_preserveRightProgram runtimeLeftShiftProgram packet
      (runtimeLeftShiftBits packet
        (packetInputArity packet + packetNativeClauseBits packet) digit)
      (runtimeLeftShiftFuel
        (packetInputArity packet + packetNativeClauseBits packet) digit)
      (runtimeLeftShiftInput
        (packetInputArity packet + packetNativeClauseBits packet) digit)
      (low + scaledClause)
      (2 ^ (packetInputArity packet + packetNativeClauseBits packet) * digit)
      (run_runtimeLeftShiftProgram packet
        (packetInputArity packet + packetNativeClauseBits packet) digit))

/-! ### The native occurrence code chain -/

private def runtimeBlockNativeCodeTailThree : NPOracleProgram :=
  linkPrograms runtimeBlockDigitShiftStageProgram blockCodeSumProgram

private def runtimeBlockNativeCodeTailTwo : NPOracleProgram :=
  linkPrograms runtimeBlockClauseShiftStageProgram
    runtimeBlockNativeCodeTailThree

private def runtimeBlockNativeCodeTailOne : NPOracleProgram :=
  linkPrograms runtimeBlockClauseStageProgram runtimeBlockNativeCodeTailTwo

/-- **The native occurrence code, computed.**  One fixed oracle-free program
turning one block window into the occurrence request payload of
`CaseTwoOccurrenceProgram`, with all four widths read from the packet. -/
def runtimeBlockNativeCodeProgram : NPOracleProgram :=
  linkPrograms runtimeBlockLowStageProgram runtimeBlockNativeCodeTailOne

theorem runtimeBlockNativeCodeProgram_oracleFree :
    OracleFree runtimeBlockNativeCodeProgram := by
  apply oracleFree_linkPrograms runtimeBlockLowStageProgram_oracleFree
  apply oracleFree_linkPrograms runtimeBlockClauseStageProgram_oracleFree
  apply oracleFree_linkPrograms runtimeBlockClauseShiftStageProgram_oracleFree
  exact oracleFree_linkPrograms runtimeBlockDigitShiftStageProgram_oracleFree
    blockCodeSumProgram_oracleFree

def runtimeBlockNativeCodeFuel (packet window : ℕ) : ℕ :=
  linkFuel runtimeBlockNativeCodeTailOne (runtimeBlockLowStageFuel packet) <|
    linkFuel runtimeBlockNativeCodeTailTwo
      (runtimeBlockClauseStageFuel packet) <|
      linkFuel runtimeBlockNativeCodeTailThree
        (runtimeBlockClauseShiftStageFuel packet
          (bitSlice (packetPaddedInputBits packet)
            (packetNativeClauseBits packet) window)) <|
        linkFuel blockCodeSumProgram
          (runtimeBlockDigitShiftStageFuel packet
            (window.testBit
                (packetPaddedInputBits packet +
                  packetPaddedClauseBits packet)).toNat)
          4

def runtimeBlockNativeCodeBits (packet window : ℕ) : ℕ :=
  occurrenceStageBits packet (runtimeBlockLowStageBits packet window) <|
    occurrenceStageBits packet
      (runtimeBlockClauseStageBits packet
        (bitSlice 0 (packetInputArity packet) window)
        (window.testBit
            (packetPaddedInputBits packet +
              packetPaddedClauseBits packet)).toNat window) <|
      occurrenceStageBits packet
        (runtimeBlockClauseShiftStageBits packet
          (bitSlice (packetPaddedInputBits packet)
            (packetNativeClauseBits packet) window)
          (bitSlice 0 (packetInputArity packet) window)
          (window.testBit
              (packetPaddedInputBits packet +
                packetPaddedClauseBits packet)).toNat) <|
        occurrenceStageBits packet
          (runtimeBlockDigitShiftStageBits packet
            (2 ^ packetInputArity packet *
              bitSlice (packetPaddedInputBits packet)
                (packetNativeClauseBits packet) window)
            (bitSlice 0 (packetInputArity packet) window)
            (window.testBit
                (packetPaddedInputBits packet +
                  packetPaddedClauseBits packet)).toNat)
          (blockCodeSumBits
            (2 ^ (packetInputArity packet + packetNativeClauseBits packet) *
              (window.testBit
                  (packetPaddedInputBits packet +
                    packetPaddedClauseBits packet)).toNat)
            (bitSlice 0 (packetInputArity packet) window +
              2 ^ packetInputArity packet *
                bitSlice (packetPaddedInputBits packet)
                  (packetNativeClauseBits packet) window))

theorem run_runtimeBlockNativeCodeProgram (packet window : ℕ) :
    runNPOracleProgram runtimeBlockNativeCodeProgram
        (runtimeBlockNativeCodeBits packet window)
        (runtimeBlockNativeCodeFuel packet window)
        (initialNPOracleState packet window) =
      some
        (nativeOccurrenceCode (packetInputArity packet)
          (packetPaddedInputBits packet) (packetNativeClauseBits packet)
          (packetPaddedClauseBits packet) window) := by
  rw [nativeOccurrenceCode]
  exact run_occurrenceStage (run_runtimeBlockLowStageProgram packet window)
    (run_occurrenceStage
      (run_runtimeBlockClauseStageProgram packet
        (bitSlice 0 (packetInputArity packet) window)
        (window.testBit
            (packetPaddedInputBits packet +
              packetPaddedClauseBits packet)).toNat window)
      (run_occurrenceStage
        (run_runtimeBlockClauseShiftStageProgram packet
          (bitSlice (packetPaddedInputBits packet)
            (packetNativeClauseBits packet) window)
          (bitSlice 0 (packetInputArity packet) window)
          (window.testBit
              (packetPaddedInputBits packet +
                packetPaddedClauseBits packet)).toNat)
        (run_occurrenceStage
          (run_runtimeBlockDigitShiftStageProgram packet
            (2 ^ packetInputArity packet *
              bitSlice (packetPaddedInputBits packet)
                (packetNativeClauseBits packet) window)
            (bitSlice 0 (packetInputArity packet) window)
            (window.testBit
                (packetPaddedInputBits packet +
                  packetPaddedClauseBits packet)).toNat)
          (run_blockCodeSumProgram packet
            (2 ^ (packetInputArity packet + packetNativeClauseBits packet) *
              (window.testBit
                  (packetPaddedInputBits packet +
                    packetPaddedClauseBits packet)).toNat)
            (bitSlice 0 (packetInputArity packet) window +
              2 ^ packetInputArity packet *
                bitSlice (packetPaddedInputBits packet)
                  (packetNativeClauseBits packet) window)))))

/-! ## 6. The assembled per-block occurrence callee -/

private def runtimeBlockOccurrenceTailTwo
    (factory : ExecutablePointwisePCPPFactory) : NPOracleProgram :=
  linkPrograms runtimeBlockOccurrenceFramePrepProgram
    (caseTwoOccurrenceProgram factory)

private def runtimeBlockOccurrenceTailOne
    (factory : ExecutablePointwisePCPPFactory) : NPOracleProgram :=
  linkPrograms runtimeBlockNativeCodeProgram
    (runtimeBlockOccurrenceTailTwo factory)

/-- **The per-block Case-2 occurrence callee, without immediates.**  One fixed
oracle-free program, parameterized only by the published factory, receiving
`pair block pointCode` at a packet-valued public length and returning the
honest occurrence bit of that block's occurrence code. -/
def runtimeCaseTwoBlockOccurrenceProgram
    (factory : ExecutablePointwisePCPPFactory) : NPOracleProgram :=
  linkPrograms runtimeBlockWindowProgram (runtimeBlockOccurrenceTailOne factory)

theorem runtimeCaseTwoBlockOccurrenceProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (runtimeCaseTwoBlockOccurrenceProgram factory) := by
  apply oracleFree_linkPrograms runtimeBlockWindowProgram_oracleFree
  apply oracleFree_linkPrograms runtimeBlockNativeCodeProgram_oracleFree
  exact oracleFree_linkPrograms
    runtimeBlockOccurrenceFramePrepProgram_oracleFree
    (caseTwoOccurrenceProgram_oracleFree factory)

def runtimeCaseTwoBlockOccurrenceFuel
    (factory : ExecutablePointwisePCPPFactory) (packet : ℕ) {n : ℕ}
    (circuit : BooleanCircuit n) (block pointCode : ℕ) : ℕ :=
  linkFuel (runtimeBlockOccurrenceTailOne factory)
    (runtimeBlockWindowFuel packet) <|
    linkFuel (runtimeBlockOccurrenceTailTwo factory)
      (runtimeBlockNativeCodeFuel packet
        (bitSlice (block * packetArity packet) (packetArity packet)
          pointCode)) <|
      linkFuel (caseTwoOccurrenceProgram factory) 13
        (caseTwoOccurrenceFuel factory packet circuit
          (caseTwoBlockOccurrenceCode (packetInputArity packet)
            (packetPaddedInputBits packet) (packetNativeClauseBits packet)
            (packetPaddedClauseBits packet) (packetArity packet) pointCode
            block))

noncomputable def runtimeCaseTwoBlockOccurrenceBits
    (factory : ExecutablePointwisePCPPFactory) (packet : ℕ) {n : ℕ}
    (circuit : BooleanCircuit n) (block pointCode : ℕ) : ℕ :=
  occurrenceStageBits packet
    (runtimeBlockWindowBits packet block pointCode) <|
    occurrenceStageBits packet
      (runtimeBlockNativeCodeBits packet
        (bitSlice (block * packetArity packet) (packetArity packet)
          pointCode)) <|
      occurrenceStageBits packet
        (runtimeBlockOccurrenceFramePrepBits packet
          (caseTwoBlockOccurrenceCode (packetInputArity packet)
            (packetPaddedInputBits packet) (packetNativeClauseBits packet)
            (packetPaddedClauseBits packet) (packetArity packet) pointCode
            block))
        (caseTwoOccurrenceBits factory packet circuit
          (caseTwoBlockOccurrenceCode (packetInputArity packet)
            (packetPaddedInputBits packet) (packetNativeClauseBits packet)
            (packetPaddedClauseBits packet) (packetArity packet) pointCode
            block))

/-- **Exact execution of the immediate-free per-block occurrence callee.**
From `pair block pointCode` and the packet in the public length register alone,
the fixed program returns the honest occurrence bit of the published factory at
the occurrence code of that block's window of the requested point. -/
theorem run_runtimeCaseTwoBlockOccurrenceProgram
    (factory : ExecutablePointwisePCPPFactory) (packet : ℕ) {n : ℕ}
    (circuit : BooleanCircuit n) (block pointCode : ℕ)
    (harity : packetInputArity packet = n)
    (hsize : packetCircuitSize packet = circuit.size)
    (hencoded : packetEncoded packet = encodeBooleanCircuit circuit) :
    runNPOracleProgram (runtimeCaseTwoBlockOccurrenceProgram factory)
        (runtimeCaseTwoBlockOccurrenceBits factory packet circuit block
          pointCode)
        (runtimeCaseTwoBlockOccurrenceFuel factory packet circuit block
          pointCode)
        (initialNPOracleState packet (Nat.pair block pointCode)) =
      some
        (caseTwoBlockValue factory circuit (packetInputArity packet)
          (packetPaddedInputBits packet) (packetNativeClauseBits packet)
          (packetPaddedClauseBits packet) (packetArity packet) pointCode
          block).toNat := by
  subst harity
  have hframe :=
    run_runtimeBlockOccurrenceFramePrepProgram packet
      (caseTwoBlockOccurrenceCode (packetInputArity packet)
        (packetPaddedInputBits packet) (packetNativeClauseBits packet)
        (packetPaddedClauseBits packet) (packetArity packet) pointCode block)
  rw [hsize, hencoded] at hframe
  exact run_occurrenceStage
    (run_runtimeBlockWindowProgram packet block pointCode)
    (run_occurrenceStage
      (run_runtimeBlockNativeCodeProgram packet
        (bitSlice (block * packetArity packet) (packetArity packet) pointCode))
      (run_occurrenceStage hframe
        (run_caseTwoOccurrenceProgram factory packet circuit
          (caseTwoBlockOccurrenceCode (packetInputArity packet)
            (packetPaddedInputBits packet) (packetNativeClauseBits packet)
            (packetPaddedClauseBits packet) (packetArity packet) pointCode
            block))))

/-! ## 7. Entering the callee at a computed packet

The callee of §6 runs at a packet-valued public length, while the Case-2 block
list calls its per-block parameter at the *target's* public length with the
bare `pair block pointCode`.  The three adapters below close that gap without
touching either ABI: reload the public length, run a packet producer on it,
frame the result as a native context call, and project the returned bit.  The
packet producer is a parameter here; §2 of the closure module supplies it. -/

/-- Reload the public length beside the retained request. -/
def occurrencePacketLiftProgram : NPOracleProgram :=
  [ .pair 1 0 0 1
  , .halt 0
  ]

@[simp] theorem occurrencePacketLiftProgram_oracleFree :
    OracleFree occurrencePacketLiftProgram := by
  rfl

def occurrencePacketLiftBits (inputLength word : ℕ) : ℕ :=
  natBitLength (Nat.pair inputLength word)

theorem run_occurrencePacketLiftProgram (inputLength word : ℕ) :
    runNPOracleProgram occurrencePacketLiftProgram
        (occurrencePacketLiftBits inputLength word) 2
        (initialNPOracleState inputLength word) =
      some (Nat.pair inputLength word) := by
  have houtput :
      natBitLength (Nat.pair inputLength word) ≤
        occurrencePacketLiftBits inputLength word := le_refl _
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputLength word) (by rfl) rfl
    (by simp [initialNPOracleState]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- Frame the computed packet and the retained request as a native context
call: the packet becomes the callee's public length. -/
def occurrencePacketFrameCoreProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .pair 2 4 5 4
  , .pair 3 5 0 5
  , .halt 0
  ]

@[simp] theorem occurrencePacketFrameCoreProgram_oracleFree :
    OracleFree occurrencePacketFrameCoreProgram := by
  rfl

def occurrencePacketFrameCoreBits (packet word : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair packet word) (Nat.pair word (Nat.pair packet 0)))

theorem run_occurrencePacketFrameCoreProgram
    (inputLength packet word : ℕ) :
    runNPOracleProgram occurrencePacketFrameCoreProgram
        (occurrencePacketFrameCoreBits packet word) 6
        (initialNPOracleState inputLength (Nat.pair packet word)) =
      some (Nat.pair word (Nat.pair packet 0)) := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair packet word →
      natBitLength value ≤ occurrencePacketFrameCoreBits packet word :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ, value ≤ Nat.pair word (Nat.pair packet 0) →
      natBitLength value ≤ occurrencePacketFrameCoreBits packet word :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hpacket := hrequest packet (Nat.left_le_pair _ _)
  have hword := hrequest word (Nat.right_le_pair _ _)
  have hzero := hresult 0 (Nat.zero_le _)
  have hframe :=
    hresult (Nat.pair packet 0) (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := packet) (by rfl) rfl
    (by simp [initialNPOracleState]) hpacket]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := word) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hword]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair packet 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hframe]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair word (Nat.pair packet 0))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtput

/-- The packet producer, framed as a native context call. -/
def occurrencePacketFrameProgram (packetProgram : NPOracleProgram) :
    NPOracleProgram :=
  linkPrograms occurrencePacketLiftProgram
    (linkPrograms (preserveRightProgram packetProgram)
      occurrencePacketFrameCoreProgram)

theorem occurrencePacketFrameProgram_oracleFree
    {packetProgram : NPOracleProgram} (hpacket : OracleFree packetProgram) :
    OracleFree (occurrencePacketFrameProgram packetProgram) := by
  apply oracleFree_linkPrograms occurrencePacketLiftProgram_oracleFree
  exact oracleFree_linkPrograms
    (preserveRightProgram_oracleFree packetProgram hpacket)
    occurrencePacketFrameCoreProgram_oracleFree

def occurrencePacketFrameFuel
    (packetProgram : NPOracleProgram) (packetFuel : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram packetProgram)
      occurrencePacketFrameCoreProgram) 2 <|
    linkFuel occurrencePacketFrameCoreProgram (preserveRightFuel packetFuel) 6

def occurrencePacketFrameBits
    (inputLength word packet packetBits : ℕ) : ℕ :=
  occurrenceStageBits inputLength (occurrencePacketLiftBits inputLength word) <|
    occurrenceStageBits inputLength
      (preserveRightBits packetBits inputLength word packet)
      (occurrencePacketFrameCoreBits packet word)

theorem run_occurrencePacketFrameProgram (packetProgram : NPOracleProgram)
    (inputLength word packet packetBits packetFuel : ℕ)
    (hpacket :
      runNPOracleProgram packetProgram packetBits packetFuel
          (initialNPOracleState inputLength inputLength) = some packet) :
    runNPOracleProgram (occurrencePacketFrameProgram packetProgram)
        (occurrencePacketFrameBits inputLength word packet packetBits)
        (occurrencePacketFrameFuel packetProgram packetFuel)
        (initialNPOracleState inputLength word) =
      some (Nat.pair word (Nat.pair packet 0)) :=
  run_occurrenceStage (run_occurrencePacketLiftProgram inputLength word)
    (run_occurrenceStage
      (run_preserveRightProgram packetProgram inputLength packetBits packetFuel
        inputLength word packet hpacket)
      (run_occurrencePacketFrameCoreProgram inputLength packet word))

/-- **The per-block occurrence callee at the target's own public length.**  One
fixed program: compute the packet from the public length, enter the
immediate-free callee of §6 at that packet, and project the returned bit. -/
def occurrenceCalleeProgram (factory : ExecutablePointwisePCPPFactory)
    (packetProgram : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (occurrencePacketFrameProgram packetProgram)
    (linkPrograms
      (nativeContextCallProgram (runtimeCaseTwoBlockOccurrenceProgram factory))
      caseTwoBlockTakeLeftProgram)

theorem occurrenceCalleeProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory)
    {packetProgram : NPOracleProgram} (hpacket : OracleFree packetProgram) :
    OracleFree (occurrenceCalleeProgram factory packetProgram) := by
  apply oracleFree_linkPrograms (occurrencePacketFrameProgram_oracleFree hpacket)
  apply oracleFree_linkPrograms
  · exact nativeContextCallProgram_oracleFree
      (runtimeCaseTwoBlockOccurrenceProgram_oracleFree factory)
  exact caseTwoBlockTakeLeftProgram_oracleFree

def occurrenceCalleeFuel (factory : ExecutablePointwisePCPPFactory)
    (packetProgram : NPOracleProgram) (packet packetFuel : ℕ) {n : ℕ}
    (circuit : BooleanCircuit n) (block pointCode : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (nativeContextCallProgram (runtimeCaseTwoBlockOccurrenceProgram factory))
      caseTwoBlockTakeLeftProgram)
    (occurrencePacketFrameFuel packetProgram packetFuel) <|
    linkFuel caseTwoBlockTakeLeftProgram
      (nativeContextCallFuel (runtimeCaseTwoBlockOccurrenceProgram factory)
        (runtimeCaseTwoBlockOccurrenceFuel factory packet circuit block
          pointCode)
        packet (Nat.pair block pointCode))
      2

noncomputable def occurrenceCalleeBits
    (factory : ExecutablePointwisePCPPFactory)
    (inputLength packet packetBits : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (block pointCode value : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (occurrencePacketFrameBits inputLength (Nat.pair block pointCode) packet
      packetBits) <|
    occurrenceStageBits inputLength
      (nativeContextCallBits inputLength packet (Nat.pair block pointCode) 0
        value
        (runtimeCaseTwoBlockOccurrenceBits factory packet circuit block
          pointCode))
      (natBitLength value)

/-- **The callee, executed from the bare request.**  Given only that the packet
producer emits the packet at the public length, the assembled stream returns
the honest occurrence bit of the requested block. -/
theorem run_occurrenceCalleeProgram (factory : ExecutablePointwisePCPPFactory)
    (packetProgram : NPOracleProgram)
    (inputLength packet packetBits packetFuel : ℕ) {n : ℕ}
    (circuit : BooleanCircuit n) (block pointCode : ℕ)
    (hpacket :
      runNPOracleProgram packetProgram packetBits packetFuel
          (initialNPOracleState inputLength inputLength) = some packet)
    (harity : packetInputArity packet = n)
    (hsize : packetCircuitSize packet = circuit.size)
    (hencoded : packetEncoded packet = encodeBooleanCircuit circuit) :
    runNPOracleProgram (occurrenceCalleeProgram factory packetProgram)
        (occurrenceCalleeBits factory inputLength packet packetBits circuit
          block pointCode
          (caseTwoBlockValue factory circuit (packetInputArity packet)
            (packetPaddedInputBits packet) (packetNativeClauseBits packet)
            (packetPaddedClauseBits packet) (packetArity packet) pointCode
            block).toNat)
        (occurrenceCalleeFuel factory packetProgram packet packetFuel circuit
          block pointCode)
        (initialNPOracleState inputLength (Nat.pair block pointCode)) =
      some
        (caseTwoBlockValue factory circuit (packetInputArity packet)
          (packetPaddedInputBits packet) (packetNativeClauseBits packet)
          (packetPaddedClauseBits packet) (packetArity packet) pointCode
          block).toNat :=
  run_occurrenceStage
    (run_occurrencePacketFrameProgram packetProgram inputLength
      (Nat.pair block pointCode) packet packetBits packetFuel hpacket)
    (run_occurrenceStage
      (run_nativeContextCallProgram
        (runtimeCaseTwoBlockOccurrenceProgram factory) inputLength packet
        (Nat.pair block pointCode) 0 _
        (runtimeCaseTwoBlockOccurrenceBits factory packet circuit block
          pointCode)
        (runtimeCaseTwoBlockOccurrenceFuel factory packet circuit block
          pointCode)
        (run_runtimeCaseTwoBlockOccurrenceProgram factory packet circuit block
          pointCode harity hsize hencoded))
      (run_caseTwoBlockTakeLeftProgram inputLength _ (Nat.pair packet 0)
        (le_refl _)))

end NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
