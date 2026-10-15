import Proof.MachineModel.CanonicalNativeModProgram
import Proof.MachineModel.PreserveRightProgram
import Proof.Foundations.VerifiedLinker

/-!
# Fixed external-literal decoder

The projection decision runner returns arbitrary natural codes.  Its semantic
interface decodes a literal by unpairing the code, reducing the tag modulo two,
and reducing the index modulo the positive query arity.  This module performs
that same operation with fixed programs, reusing the canonical remainder
machine for the only nontrivial arithmetic step.
-/

namespace NearCubicWires.CanonicalLiteralDecodeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeModProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def literalDecodeInput (arity code : ℕ) : ℕ :=
  Nat.pair code arity

def literalDecodeOutput (arity code : ℕ) : ℕ :=
  let fields := Nat.unpair code
  Nat.pair (fields.1.testBit 0).toNat (fields.2 % arity)

/-- The executable result is exactly the public semantic decoder re-encoded in
the canonical literal representation. -/
theorem literalDecodeOutput_eq_encodeLiteral
    (arity code : ℕ) (harity : 0 < arity) :
    literalDecodeOutput arity code =
      encodeLiteral (decodeLiteral harity code) := by
  let fields := Nat.unpair code
  by_cases htag : fields.1 % 2 = 0
  · have hbit : fields.1.testBit 0 = false :=
      Nat.mod_two_eq_zero_iff_testBit_zero.mp htag
    simp [literalDecodeOutput, decodeLiteral, fields, htag, hbit,
      encodeLiteral]
  · have hmod : fields.1 % 2 = 1 := by
      have hlt := Nat.mod_lt fields.1 (by omega : 0 < 2)
      omega
    have hbit : fields.1.testBit 0 = true :=
      Nat.mod_two_eq_one_iff_testBit_zero.mp hmod
    simp [literalDecodeOutput, decodeLiteral, fields, htag, hbit,
      encodeLiteral]

/-- Prepare `pair(pair(rawIndex, arity), rawTag)`.  The right component is
preserved around the single shared remainder call. -/
def literalDecodePrepareProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .pair 5 3 5 5
  , .pair 5 4 0 6
  , .halt 0
  ]

@[simp] theorem literalDecodePrepareProgram_oracleFree :
    OracleFree literalDecodePrepareProgram := by
  rfl

def literalDecodePrepared (arity code : ℕ) : ℕ :=
  let fields := Nat.unpair code
  Nat.pair (nativeModInput fields.2 arity) fields.1

def literalDecodePrepareBits (arity code : ℕ) : ℕ :=
  max
    (natBitLength (literalDecodeInput arity code))
    (natBitLength (literalDecodePrepared arity code))

theorem run_literalDecodePrepareProgram
    (inputLength arity code : ℕ) :
    runNPOracleProgram literalDecodePrepareProgram
        (literalDecodePrepareBits arity code) 7
        (initialNPOracleState inputLength
          (literalDecodeInput arity code)) =
      some (literalDecodePrepared arity code) := by
  let request := literalDecodeInput arity code
  let fields := Nat.unpair code
  let modInput := nativeModInput fields.2 arity
  let prepared := literalDecodePrepared arity code
  let maximumBits := literalDecodePrepareBits arity code
  have hrequestBits :
      natBitLength request ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpreparedBits :
      natBitLength prepared ≤ maximumBits :=
    Nat.le_max_right _ _
  have hcodeBits : natBitLength code ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hrequestBits
    simpa only [request, literalDecodeInput] using
      Nat.left_le_pair code arity
  have harityBits : natBitLength arity ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hrequestBits
    simpa only [request, literalDecodeInput] using
      Nat.right_le_pair code arity
  have htagBits :
      natBitLength fields.1 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.unpair_left_le code)).trans hcodeBits
  have hindexBits :
      natBitLength fields.2 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.unpair_right_le code)).trans hcodeBits
  have hmodInputBits :
      natBitLength modInput ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hpreparedBits
    simpa only [prepared, literalDecodePrepared] using
      Nat.left_le_pair modInput fields.1
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := code)
    (by rfl) rfl
    (by simp [initialNPOracleState, literalDecodeInput])
    hcodeBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := arity)
    (by rfl) rfl
    (by simp [initialNPOracleState, literalDecodeInput])
    harityBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := fields.1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, fields])
    htagBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := fields.2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, fields])
    hindexBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := modInput)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, modInput,
      nativeModInput])
    hmodInputBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := prepared)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, prepared,
      literalDecodePrepared, modInput, fields])
    hpreparedBits]
  exact run_halt_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, prepared])
    hpreparedBits

/-- Convert `pair(index % arity, rawTag)` to the canonical literal code
`pair(rawTag % 2, index % arity)`.  Bit zero is exactly reduction modulo two. -/
def literalDecodeFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .set 4 0 3
  , .testBit 3 4 3 4
  , .pair 3 2 0 5
  , .halt 0
  ]

@[simp] theorem literalDecodeFinishProgram_oracleFree :
    OracleFree literalDecodeFinishProgram := by
  rfl

def literalDecodeFinished (remainder tag : ℕ) : ℕ :=
  Nat.pair (tag.testBit 0).toNat remainder

def literalDecodeFinishBits (remainder tag : ℕ) : ℕ :=
  max
    (natBitLength (Nat.pair remainder tag))
    (natBitLength (literalDecodeFinished remainder tag))

theorem run_literalDecodeFinishProgram
    (inputLength remainder tag : ℕ) :
    runNPOracleProgram literalDecodeFinishProgram
        (literalDecodeFinishBits remainder tag) 6
        (initialNPOracleState inputLength (Nat.pair remainder tag)) =
      some (literalDecodeFinished remainder tag) := by
  let output := literalDecodeFinished remainder tag
  let maximumBits := literalDecodeFinishBits remainder tag
  have hinputBits :
      natBitLength (Nat.pair remainder tag) ≤ maximumBits :=
    Nat.le_max_left _ _
  have houtputBits :
      natBitLength output ≤ maximumBits :=
    Nat.le_max_right _ _
  have hremainderBits :
      natBitLength remainder ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair remainder tag)).trans hinputBits
  have htagBits :
      natBitLength tag ≤ maximumBits :=
    (natBitLength_mono
      (Nat.right_le_pair remainder tag)).trans hinputBits
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le remainder)).trans hremainderBits
  have htagBitBits :
      natBitLength (tag.testBit 0).toNat ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans houtputBits
    simpa only [output, literalDecodeFinished] using
      Nat.left_le_pair (tag.testBit 0).toNat remainder
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := remainder)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hremainderBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := tag)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    htagBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzeroBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_testBit_instruction (value := (tag.testBit 0).toNat)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htagBitBits]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output,
      literalDecodeFinished])
    houtputBits]
  exact run_halt_instruction (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtputBits

def literalDecodeRemainderProgram : NPOracleProgram :=
  preserveRightProgram nativeModProgram

def literalDecodeCoreProgram : NPOracleProgram :=
  linkPrograms literalDecodeRemainderProgram
    literalDecodeFinishProgram

def literalDecodeProgram : NPOracleProgram :=
  linkPrograms literalDecodePrepareProgram literalDecodeCoreProgram

@[simp] theorem literalDecodeProgram_oracleFree :
    OracleFree literalDecodeProgram := by
  apply oracleFree_linkPrograms literalDecodePrepareProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree nativeModProgram
      nativeModProgram_oracleFree
  · exact literalDecodeFinishProgram_oracleFree

def literalDecodeRemainderFuel
    (arity code : ℕ) : ℕ :=
  preserveRightFuel <|
    nativeModFuel (Nat.unpair code).2 arity

def literalDecodeCoreFuel
    (arity code : ℕ) : ℕ :=
  linkFuel literalDecodeFinishProgram
    (literalDecodeRemainderFuel arity code) 6

def literalDecodeFuel (arity code : ℕ) : ℕ :=
  linkFuel literalDecodeCoreProgram 7
    (literalDecodeCoreFuel arity code)

theorem literalDecodeFuel_le (arity code : ℕ) :
    literalDecodeFuel arity code ≤
      7 * (Nat.unpair code).2 + 57 := by
  have hfinishSpan :
      programRegisterSpan literalDecodeFinishProgram = 5 := by
    decide
  have hcoreSpan :
      programRegisterSpan literalDecodeCoreProgram = 15 := by
    decide
  rw [literalDecodeFuel, linkFuel_exact,
    literalDecodeCoreFuel, linkFuel_exact,
    hfinishSpan, hcoreSpan]
  have hmod :=
    nativeModFuel_le (Nat.unpair code).2 arity
  simp only [literalDecodeRemainderFuel,
    PreserveRightProgram.preserveRightFuel] at *
  omega

def literalDecodeBits
    (inputLength arity code : ℕ) : ℕ :=
  let fields := Nat.unpair code
  let modInput := nativeModInput fields.2 arity
  let remainder := fields.2 % arity
  max (natBitLength inputLength) <|
    max (literalDecodePrepareBits arity code) <|
      max
        (preserveRightBits (nativeModBits fields.2 arity)
          modInput fields.1 remainder)
        (literalDecodeFinishBits remainder fields.1)

theorem run_literalDecodeProgram
    (inputLength arity code : ℕ) (harity : 0 < arity) :
    runNPOracleProgram literalDecodeProgram
        (literalDecodeBits inputLength arity code)
        (literalDecodeFuel arity code)
        (initialNPOracleState inputLength
          (literalDecodeInput arity code)) =
      some (literalDecodeOutput arity code) := by
  let fields := Nat.unpair code
  let modInput := nativeModInput fields.2 arity
  let remainder := fields.2 % arity
  let prepared := literalDecodePrepared arity code
  let preserved := Nat.pair remainder fields.1
  let maximumBits := literalDecodeBits inputLength arity code
  let prepareBits := literalDecodePrepareBits arity code
  let modBits := nativeModBits fields.2 arity
  let preserveBits :=
    preserveRightBits modBits modInput fields.1 remainder
  let finishBits := literalDecodeFinishBits remainder fields.1
  have hlengthBits :
      natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hprepareBits : prepareBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits : preserveBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hfinishBits : finishBits ≤ maximumBits := by
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive : 1 ≤ maximumBits := by
    exact (by
      unfold natBitLength
      omega : 1 ≤ natBitLength inputLength).trans hlengthBits
  have hprepare :
      runNPOracleProgram literalDecodePrepareProgram maximumBits 7
          (initialNPOracleState inputLength
            (literalDecodeInput arity code)) =
        some prepared := by
    exact run_bits_mono
      (run_literalDecodePrepareProgram inputLength arity code)
      hprepareBits
  have hmodAtOwnBits :
      runNPOracleProgram nativeModProgram modBits
          (nativeModFuel fields.2 arity)
          (initialNPOracleState inputLength modInput) =
        some remainder := by
    simpa only [fields, modInput, modBits, remainder] using
      run_nativeModProgram inputLength fields.2 arity harity
  have hpreserveAtOwnBits :
      runNPOracleProgram literalDecodeRemainderProgram preserveBits
          (literalDecodeRemainderFuel arity code)
          (initialNPOracleState inputLength prepared) =
        some preserved := by
    simpa only [literalDecodeRemainderProgram,
      literalDecodeRemainderFuel, fields, modInput, remainder,
      prepared, literalDecodePrepared, preserved, preserveBits,
      modBits] using
        run_preserveRightProgram nativeModProgram inputLength
          modBits (nativeModFuel fields.2 arity)
          modInput fields.1 remainder hmodAtOwnBits
  have hpreserve :
      runNPOracleProgram literalDecodeRemainderProgram maximumBits
          (literalDecodeRemainderFuel arity code)
          (initialNPOracleState inputLength prepared) =
        some preserved :=
    run_bits_mono hpreserveAtOwnBits hpreserveBits
  have hfinish :
      runNPOracleProgram literalDecodeFinishProgram maximumBits 6
          (initialNPOracleState inputLength preserved) =
        some (literalDecodeOutput arity code) := by
    have hrun := run_bits_mono
      (run_literalDecodeFinishProgram inputLength remainder fields.1)
      hfinishBits
    simpa only [preserved, literalDecodeOutput, fields,
      literalDecodeFinished, remainder] using hrun
  have hcore :
      runNPOracleProgram literalDecodeCoreProgram maximumBits
          (literalDecodeCoreFuel arity code)
          (initialNPOracleState inputLength prepared) =
        some (literalDecodeOutput arity code) := by
    exact run_linkPrograms hpositive hlengthBits hpreserve hfinish
  exact run_linkPrograms hpositive hlengthBits hprepare hcore

theorem run_literalDecodeProgram_eq_encodeLiteral
    (inputLength arity code : ℕ) (harity : 0 < arity) :
    runNPOracleProgram literalDecodeProgram
        (literalDecodeBits inputLength arity code)
        (literalDecodeFuel arity code)
        (initialNPOracleState inputLength
          (literalDecodeInput arity code)) =
      some (encodeLiteral (decodeLiteral harity code)) := by
  rw [run_literalDecodeProgram inputLength arity code harity,
    literalDecodeOutput_eq_encodeLiteral arity code harity]

end NearCubicWires.CanonicalLiteralDecodeProgram
