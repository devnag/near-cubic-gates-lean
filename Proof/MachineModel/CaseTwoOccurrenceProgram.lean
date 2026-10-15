import Proof.MachineModel.CanonicalLiteralDecodeProgram
import Proof.MachineModel.CaseTwoOccurrenceParityProgram
import Proof.CaseAnalysis.CaseTwoOccurrenceRunnerCalls
import Proof.MachineModel.TaggedProgramChoice

/-!
# The assembled Case-2 occurrence program

`CaseTwoOccurrenceEvaluation.executableOccurrenceValue_prefixView` reduces one
honest occurrence bit of the published factory to `occurrenceCodeValue`: four
runner executions, one interior digit window, one masked parity fold, and one
digit read.  Every one of those pieces already has an exact interpreter run:

* `CaseTwoOccurrenceRunnerCalls.run_shapeCallProgram`, `…_clauseCallProgram`,
  `…_supportCallProgram`, `…_honestCallProgram`;
* `CanonicalBitSliceProgram.run_bitSliceProgram`;
* `CanonicalLiteralDecodeProgram.run_literalDecodeProgram`;
* `CaseTwoOccurrenceParityProgram.run_maskedParityProgram`.

This module supplies the missing wiring and nothing else.  Every declaration
below is either one straight-line framing adapter — a fixed sequence of
`unpair`, `pair`, `add`, `subtract`, and `testBit` instructions moving already
computed naturals between the published call ABIs — or one application of the
verified linker, the count-preserving wrapper, and the fixed tag dispatcher.
No new mathematics, no callback, and no second occurrence convention is
introduced.

The single assignment dispatch is the saturating difference
`systematicBits - index`: it vanishes exactly on the auxiliary indices.  One
`supportRunner` call therefore suffices per occurrence, because the selected
literal names a single assignment coordinate.
-/

namespace NearCubicWires.CaseTwoOccurrenceProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalLiteralDecodeProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceParityProgram
open NearCubicWires.CaseTwoOccurrenceRunnerCalls
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.UnaryPolynomialSelector
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping shared by every framing adapter -/

private theorem digit_bits {digit bound : ℕ} (hdigit : digit ≤ 1) :
    natBitLength digit ≤ natBitLength bound := by
  have hone : 1 ≤ natBitLength bound := by
    unfold natBitLength
    omega
  have hsmall : natBitLength digit ≤ 1 := by
    interval_cases digit <;> simp [natBitLength]
  omega

private theorem toNat_le_one (value : Bool) : value.toNat ≤ 1 := by
  cases value <;> simp

private theorem le_pair_of_le_left {value left right : ℕ}
    (hvalue : value ≤ left) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.left_le_pair left right)

private theorem le_pair_of_le_right {value left right : ℕ}
    (hvalue : value ≤ right) : value ≤ Nat.pair left right :=
  hvalue.trans (Nat.right_le_pair left right)

/-! ## 2. The framing words

Six fixed context words carry the already computed naturals of one occurrence
between the published call ABIs.  Each is a right-nested `Nat.pair` chain, so
every field is bounded by the word itself and no adapter needs a width
argument of its own. -/

/-- Context while the shape call is in flight: circuit arity, encoded circuit,
and the public occurrence code. -/
def occurrenceContextZero (inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair inputArity (Nat.pair encoded inputCode)

/-- Context after the shape widths are read.  The occurrence position digit is
the leading field, so the literal selector reaches it with two reads. -/
def occurrenceContextOne
    (position systematicBits assignmentBits inputArity encoded
      inputCode : ℕ) : ℕ :=
  Nat.pair position
    (Nat.pair systematicBits
      (Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode))))

/-- Context handed to both branches of the assignment dispatcher. -/
def occurrenceContextTwo
    (tag systematicBits inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair tag
    (Nat.pair systematicBits
      (Nat.pair inputArity (Nat.pair encoded inputCode)))

/-- Context of the systematic branch while its support call is in flight. -/
def occurrenceContextThree (tag inputArity inputCode : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair inputArity inputCode)

/-- Context of the auxiliary branch before its honest call. -/
def occurrenceContextFour
    (tag systematicBits index inputArity encoded : ℕ) : ℕ :=
  Nat.pair tag
    (Nat.pair systematicBits (Nat.pair index (Nat.pair inputArity encoded)))

/-- Context of the auxiliary branch after its honest call. -/
def occurrenceContextFive (tag systematicBits index : ℕ) : ℕ :=
  Nat.pair tag (Nat.pair systematicBits index)

/-- Public ABI of one Case-2 occurrence request: the circuit arity, its size,
its encoding, and the requested occurrence code. -/
def caseTwoOccurrenceInput
    (inputArity circuitSize encoded inputCode : ℕ) : ℕ :=
  Nat.pair inputArity (Nat.pair circuitSize (Nat.pair encoded inputCode))

/-! ## 3. Straight-line framing adapters -/

/-! ### 3.1 Preparing the shape call

Register ABI: `r2` arity, `r3` request tail, `r4` circuit-and-code pair, `r5`
encoded circuit, `r6` native request, `r7` context. -/

def shapePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairLeft 4 5 4
  , .pair 2 5 6 5
  , .pair 2 4 7 6
  , .pair 6 7 0 7
  , .halt 0
  ]

@[simp] theorem shapePrepProgram_oracleFree :
    OracleFree shapePrepProgram := by
  rfl

def shapePrepFuel : ℕ := 8

def shapePrepOutput (inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair (nativeInputRequest inputArity encoded)
    (occurrenceContextZero inputArity encoded inputCode)

def shapePrepBits (inputArity circuitSize encoded inputCode : ℕ) : ℕ :=
  natBitLength
    (max (caseTwoOccurrenceInput inputArity circuitSize encoded inputCode)
      (shapePrepOutput inputArity encoded inputCode))

theorem run_shapePrepProgram
    (inputLength inputArity circuitSize encoded inputCode : ℕ) :
    runNPOracleProgram shapePrepProgram
        (shapePrepBits inputArity circuitSize encoded inputCode)
        shapePrepFuel
        (initialNPOracleState inputLength
          (caseTwoOccurrenceInput inputArity circuitSize encoded inputCode)) =
      some (shapePrepOutput inputArity encoded inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        caseTwoOccurrenceInput inputArity circuitSize encoded inputCode →
      natBitLength value ≤
        shapePrepBits inputArity circuitSize encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ shapePrepOutput inputArity encoded inputCode →
      natBitLength value ≤
        shapePrepBits inputArity circuitSize encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have harity := hrequest inputArity (le_pair_of_le_left (le_refl _))
  have htail :=
    hrequest (Nat.pair circuitSize (Nat.pair encoded inputCode))
      (le_pair_of_le_right (le_refl _))
  have hcode :=
    hrequest (Nat.pair encoded inputCode)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hencoded :=
    hrequest encoded
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hnative :=
    hresult (nativeInputRequest inputArity encoded)
      (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hresult (occurrenceContextZero inputArity encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show shapePrepFuel = 7 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [initialNPOracleState, caseTwoOccurrenceInput])
    harity]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair circuitSize (Nat.pair encoded inputCode))
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
      caseTwoOccurrenceInput])
    htail]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hencoded]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := nativeInputRequest inputArity encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeInputRequest])
    hnative]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := occurrenceContextZero inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextZero])
    hcontext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := shapePrepOutput inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, shapePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.2 Reading the shape widths and preparing the clause address -/

/-- The systematic width read out of one shape code. -/
def shapeSystematicBits (shapeCode : ℕ) : ℕ :=
  (Nat.unpair shapeCode).1 + 1

/-- The auxiliary width read out of one shape code. -/
def shapeAuxiliaryBits (shapeCode : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair shapeCode).2).1

/-- The clause width read out of one shape code. -/
def shapeClauseBits (shapeCode : ℕ) : ℕ :=
  (Nat.unpair (Nat.unpair shapeCode).2).2

/-!
Register ABI: `r2` shape code, `r3` context, `r4` arity, `r5` circuit-and-code
pair, `r6` encoded circuit, `r7` occurrence code, `r8` systematic width, `r9`
shape tail, `r10` auxiliary width, `r11` clause width, `r12` assignment width,
`r13` position index, `r14` position digit, `r15` new context, `r16` slice
request.
-/
def widthPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 2 8 7
  , .unpairRight 2 9 8
  , .increment 8 9
  , .unpairLeft 9 10 10
  , .unpairRight 9 11 11
  , .add 8 10 12 12
  , .add 4 11 13 13
  , .testBit 7 13 14 14
  , .pair 6 7 15 15
  , .pair 4 15 15 16
  , .pair 12 15 15 17
  , .pair 8 15 15 18
  , .pair 14 15 15 19
  , .pair 11 7 16 20
  , .pair 4 16 16 21
  , .pair 16 15 0 22
  , .halt 0
  ]

@[simp] theorem widthPrepProgram_oracleFree :
    OracleFree widthPrepProgram := by
  rfl

def widthPrepFuel : ℕ := 23

def widthPrepOutput (shapeCode inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair (bitSliceInput inputArity (shapeClauseBits shapeCode) inputCode)
    (occurrenceContextOne
      (inputCode.testBit (inputArity + shapeClauseBits shapeCode)).toNat
      (shapeSystematicBits shapeCode)
      (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
      inputArity encoded inputCode)

def widthPrepBits (shapeCode inputArity encoded inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair shapeCode
        (occurrenceContextZero inputArity encoded inputCode))
      (max (widthPrepOutput shapeCode inputArity encoded inputCode)
        (inputArity + shapeClauseBits shapeCode)))

theorem run_widthPrepProgram
    (inputLength shapeCode inputArity encoded inputCode : ℕ) :
    runNPOracleProgram widthPrepProgram
        (widthPrepBits shapeCode inputArity encoded inputCode)
        widthPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair shapeCode
            (occurrenceContextZero inputArity encoded inputCode))) =
      some (widthPrepOutput shapeCode inputArity encoded inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair shapeCode
          (occurrenceContextZero inputArity encoded inputCode) →
      natBitLength value ≤
        widthPrepBits shapeCode inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ widthPrepOutput shapeCode inputArity encoded inputCode →
      natBitLength value ≤
        widthPrepBits shapeCode inputArity encoded inputCode :=
    fun _ hvalue =>
      natBitLength_mono
        (hvalue.trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hindex :
      natBitLength (inputArity + shapeClauseBits shapeCode) ≤
        widthPrepBits shapeCode inputArity encoded inputCode :=
    natBitLength_mono ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hshape := hrequest shapeCode (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest (occurrenceContextZero inputArity encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have harity :=
    hrequest inputArity
      (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hpairCode :=
    hrequest (Nat.pair encoded inputCode)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hencoded :=
    hrequest encoded
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hinputCode :=
    hrequest inputCode
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hpredecessor :=
    hrequest (Nat.unpair shapeCode).1
      (le_pair_of_le_left (Nat.unpair_left_le _))
  have htail :=
    hrequest (Nat.unpair shapeCode).2
      (le_pair_of_le_left (Nat.unpair_right_le _))
  have hauxiliary :=
    hrequest (shapeAuxiliaryBits shapeCode)
      (le_pair_of_le_left
        ((Nat.unpair_left_le _).trans (Nat.unpair_right_le _)))
  have hclause :=
    hrequest (shapeClauseBits shapeCode)
      (le_pair_of_le_left
        ((Nat.unpair_right_le _).trans (Nat.unpair_right_le _)))
  have hsystematic :=
    hresult (shapeSystematicBits shapeCode)
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hassignment :=
    hresult (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))))
  have hposition :
      natBitLength
          (inputCode.testBit (inputArity + shapeClauseBits shapeCode)).toNat ≤
        widthPrepBits shapeCode inputArity encoded inputCode :=
    digit_bits (toNat_le_one _)
  have hframeOne :=
    hresult (Nat.pair encoded inputCode)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))))
  have hframeTwo :=
    hresult (Nat.pair inputArity (Nat.pair encoded inputCode))
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have hframeThree :=
    hresult
      (Nat.pair (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hframeFour :=
    hresult
      (Nat.pair (shapeSystematicBits shapeCode)
        (Nat.pair
          (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hnewContext :=
    hresult
      (occurrenceContextOne
        (inputCode.testBit (inputArity + shapeClauseBits shapeCode)).toNat
        (shapeSystematicBits shapeCode)
        (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
        inputArity encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have hclauseCode :=
    hresult (Nat.pair (shapeClauseBits shapeCode) inputCode)
      (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hslice :=
    hresult (bitSliceInput inputArity (shapeClauseBits shapeCode) inputCode)
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show widthPrepFuel = 22 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := shapeCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hshape]
  rw [show 22 = 21 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := occurrenceContextZero inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 21 = 20 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextZero])
    harity]
  rw [show 20 = 19 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextZero])
    hpairCode]
  rw [show 19 = 18 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hencoded]
  rw [show 18 = 17 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCode]
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairLeft_instruction (value := (Nat.unpair shapeCode).1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpredecessor]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairRight_instruction (value := (Nat.unpair shapeCode).2)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htail]
  rw [show 15 = 14 + 1 by omega]
  rw [run_increment_instruction (value := shapeSystematicBits shapeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, shapeSystematicBits])
    hsystematic]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := shapeAuxiliaryBits shapeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, shapeAuxiliaryBits])
    hauxiliary]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction (value := shapeClauseBits shapeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, shapeClauseBits])
    hclause]
  rw [show 12 = 11 + 1 by omega]
  rw [run_add_instruction
    (value := shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hassignment]
  rw [show 11 = 10 + 1 by omega]
  rw [run_add_instruction (value := inputArity + shapeClauseBits shapeCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindex]
  rw [show 10 = 9 + 1 by omega]
  rw [run_testBit_instruction
    (value :=
      (inputCode.testBit (inputArity + shapeClauseBits shapeCode)).toNat)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hposition]
  rw [show 9 = 8 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeOne]
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair inputArity (Nat.pair encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeThree]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (shapeSystematicBits shapeCode)
        (Nat.pair
          (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeFour]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      occurrenceContextOne
        (inputCode.testBit (inputArity + shapeClauseBits shapeCode)).toNat
        (shapeSystematicBits shapeCode)
        (shapeSystematicBits shapeCode + shapeAuxiliaryBits shapeCode)
        inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextOne])
    hnewContext]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (shapeClauseBits shapeCode) inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hclauseCode]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := bitSliceInput inputArity (shapeClauseBits shapeCode) inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hslice]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := widthPrepOutput shapeCode inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, widthPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.3 Preparing the clause call -/

/-!
Register ABI: `r2` clause address, `r3` context, `r4`–`r6` context tails, `r7`
arity, `r8` circuit-and-code pair, `r9` encoded circuit, `r10` native request.
-/
def clausePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairRight 3 4 3
  , .unpairRight 4 5 4
  , .unpairRight 5 6 5
  , .unpairLeft 6 7 6
  , .unpairRight 6 8 7
  , .unpairLeft 8 9 8
  , .pair 9 2 10 9
  , .pair 7 10 10 10
  , .pair 10 3 0 11
  , .halt 0
  ]

@[simp] theorem clausePrepProgram_oracleFree :
    OracleFree clausePrepProgram := by
  rfl

def clausePrepFuel : ℕ := 12

def clausePrepOutput
    (address position systematicBits assignmentBits inputArity encoded
      inputCode : ℕ) : ℕ :=
  Nat.pair (nativeInputRequest inputArity (Nat.pair encoded address))
    (occurrenceContextOne position systematicBits assignmentBits inputArity
      encoded inputCode)

def clausePrepBits
    (address position systematicBits assignmentBits inputArity encoded
      inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair address
        (occurrenceContextOne position systematicBits assignmentBits
          inputArity encoded inputCode))
      (clausePrepOutput address position systematicBits assignmentBits
        inputArity encoded inputCode))

theorem run_clausePrepProgram
    (inputLength address position systematicBits assignmentBits inputArity
      encoded inputCode : ℕ) :
    runNPOracleProgram clausePrepProgram
        (clausePrepBits address position systematicBits assignmentBits
          inputArity encoded inputCode)
        clausePrepFuel
        (initialNPOracleState inputLength
          (Nat.pair address
            (occurrenceContextOne position systematicBits assignmentBits
              inputArity encoded inputCode))) =
      some
        (clausePrepOutput address position systematicBits assignmentBits
          inputArity encoded inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair address
          (occurrenceContextOne position systematicBits assignmentBits
            inputArity encoded inputCode) →
      natBitLength value ≤
        clausePrepBits address position systematicBits assignmentBits
          inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        clausePrepOutput address position systematicBits assignmentBits
          inputArity encoded inputCode →
      natBitLength value ≤
        clausePrepBits address position systematicBits assignmentBits
          inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have haddress := hrequest address (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest
      (occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have hframeOne :=
    hrequest
      (Nat.pair systematicBits
        (Nat.pair assignmentBits
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hframeTwo :=
    hrequest
      (Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hframeThree :=
    hrequest (Nat.pair inputArity (Nat.pair encoded inputCode))
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have harity :=
    hrequest inputArity
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))))
  have hpairCode :=
    hrequest (Nat.pair encoded inputCode)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))))
  have hencoded :=
    hrequest encoded
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right
              (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))))))
  have hcodePair :=
    hresult (Nat.pair encoded address)
      (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hnative :=
    hresult (nativeInputRequest inputArity (Nat.pair encoded address))
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show clausePrepFuel = 11 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := address)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    haddress]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair systematicBits
        (Nat.pair assignmentBits
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextOne])
    hframeOne]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair inputArity (Nat.pair encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeThree]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpairCode]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hencoded]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair encoded address)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcodePair]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := nativeInputRequest inputArity (Nat.pair encoded address))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeInputRequest])
    hnative]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      clausePrepOutput address position systematicBits assignmentBits
        inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, clausePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.4 Selecting the occurrence literal and preparing its decode -/

/-- The literal field selected by one occurrence position digit: the left
field of the clause code at digit zero, the right field otherwise. -/
def occurrenceLiteralField (clauseCode position : ℕ) : ℕ :=
  if position = 0 then (Nat.unpair clauseCode).1
  else (Nat.unpair clauseCode).2

theorem occurrenceLiteralField_le (clauseCode position : ℕ) :
    occurrenceLiteralField clauseCode position ≤ clauseCode := by
  unfold occurrenceLiteralField
  split
  · exact Nat.unpair_left_le clauseCode
  · exact Nat.unpair_right_le clauseCode

/-!
Register ABI: `r2` clause code, `r3` context, `r4` position digit, `r5`
selected literal code, `r6`–`r7` context tails, `r8` assignment width, `r9`
decode request.  Both selection arms cost the same two instructions, so the
adapter has one fuel charge.
-/
def literalPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .branchZero 4 4 6
  , .unpairLeft 2 5 5
  , .branchZero 5 8 8
  , .unpairRight 2 5 7
  , .branchZero 5 8 8
  , .unpairRight 3 6 9
  , .unpairRight 6 7 10
  , .unpairLeft 7 8 11
  , .pair 5 8 9 12
  , .pair 9 3 0 13
  , .halt 0
  ]

@[simp] theorem literalPrepProgram_oracleFree :
    OracleFree literalPrepProgram := by
  rfl

def literalPrepFuel : ℕ := 12

def literalPrepOutput
    (clauseCode position systematicBits assignmentBits inputArity encoded
      inputCode : ℕ) : ℕ :=
  Nat.pair
    (literalDecodeInput assignmentBits
      (occurrenceLiteralField clauseCode position))
    (occurrenceContextOne position systematicBits assignmentBits inputArity
      encoded inputCode)

def literalPrepBits
    (clauseCode position systematicBits assignmentBits inputArity encoded
      inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair clauseCode
        (occurrenceContextOne position systematicBits assignmentBits
          inputArity encoded inputCode))
      (literalPrepOutput clauseCode position systematicBits assignmentBits
        inputArity encoded inputCode))

/-- Common suffix of both selection arms, stated on an abstract state so no
register tower has to be spelled out. -/
private theorem run_literalPrepFinish
    (maximumBits literalCode position systematicBits assignmentBits
      inputArity encoded inputCode : ℕ)
    (state : NPOracleState) (hpc : state.pc = 8)
    (hcontextReg : state.registers 3 =
      occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
    (hliteralReg : state.registers 5 = literalCode)
    (hframeOne :
      natBitLength
          (Nat.pair systematicBits
            (Nat.pair assignmentBits
              (Nat.pair inputArity (Nat.pair encoded inputCode)))) ≤
        maximumBits)
    (hframeTwo :
      natBitLength
          (Nat.pair assignmentBits
            (Nat.pair inputArity (Nat.pair encoded inputCode))) ≤
        maximumBits)
    (hassignment : natBitLength assignmentBits ≤ maximumBits)
    (hdecode :
      natBitLength (literalDecodeInput assignmentBits literalCode) ≤
        maximumBits)
    (houtput :
      natBitLength
          (Nat.pair (literalDecodeInput assignmentBits literalCode)
            (occurrenceContextOne position systematicBits assignmentBits
              inputArity encoded inputCode)) ≤
        maximumBits) :
    runNPOracleProgram literalPrepProgram maximumBits 6 state =
      some
        (Nat.pair (literalDecodeInput assignmentBits literalCode)
          (occurrenceContextOne position systematicBits assignmentBits
            inputArity encoded inputCode)) := by
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair systematicBits
        (Nat.pair assignmentBits
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
    (by rfl) hpc
    (by simp [hcontextReg, occurrenceContextOne])
    hframeOne]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (value := assignmentBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hassignment]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := literalDecodeInput assignmentBits literalCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, literalDecodeInput,
      hliteralReg])
    hdecode]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (literalDecodeInput assignmentBits literalCode)
        (occurrenceContextOne position systematicBits assignmentBits
          inputArity encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcontextReg])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

theorem run_literalPrepProgram
    (inputLength clauseCode position systematicBits assignmentBits inputArity
      encoded inputCode : ℕ) :
    runNPOracleProgram literalPrepProgram
        (literalPrepBits clauseCode position systematicBits assignmentBits
          inputArity encoded inputCode)
        literalPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair clauseCode
            (occurrenceContextOne position systematicBits assignmentBits
              inputArity encoded inputCode))) =
      some
        (literalPrepOutput clauseCode position systematicBits assignmentBits
          inputArity encoded inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair clauseCode
          (occurrenceContextOne position systematicBits assignmentBits
            inputArity encoded inputCode) →
      natBitLength value ≤
        literalPrepBits clauseCode position systematicBits assignmentBits
          inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        literalPrepOutput clauseCode position systematicBits assignmentBits
          inputArity encoded inputCode →
      natBitLength value ≤
        literalPrepBits clauseCode position systematicBits assignmentBits
          inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hclause := hrequest clauseCode (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest
      (occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have hposition :=
    hrequest position
      (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hliteral :=
    hrequest (occurrenceLiteralField clauseCode position)
      (le_pair_of_le_left (occurrenceLiteralField_le clauseCode position))
  have hframeOne :=
    hrequest
      (Nat.pair systematicBits
        (Nat.pair assignmentBits
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hframeTwo :=
    hrequest
      (Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hassignment :=
    hrequest assignmentBits
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))))
  have hdecode :=
    hresult
      (literalDecodeInput assignmentBits
        (occurrenceLiteralField clauseCode position))
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show literalPrepFuel = 11 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := clauseCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hclause]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := position)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextOne])
    hposition]
  rw [show 9 = 8 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  rw [show
    ((((initialNPOracleState inputLength
      (Nat.pair clauseCode
        (occurrenceContextOne position systematicBits assignmentBits
          inputArity encoded inputCode))).write 2 clauseCode).jump 1).write 3
            (occurrenceContextOne position systematicBits assignmentBits
              inputArity encoded inputCode) |>.jump 2 |>.write 4
                position |>.jump 3).registers 4 = position by
    simp [NPOracleState.write, NPOracleState.jump]]
  unfold literalPrepOutput
  by_cases hzero : position = 0
  · rw [if_pos hzero]
    rw [show 8 = 7 + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := occurrenceLiteralField clauseCode position)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        occurrenceLiteralField, hzero])
      hliteral]
    rw [show 7 = 6 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    rw [ite_self]
    exact run_literalPrepFinish _ (occurrenceLiteralField clauseCode position)
      position systematicBits assignmentBits inputArity encoded inputCode _
      rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
      hframeOne hframeTwo hassignment hdecode houtput
  · rw [if_neg hzero]
    rw [show 8 = 7 + 1 by omega]
    rw [run_unpairRight_instruction
      (value := occurrenceLiteralField clauseCode position)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump,
        occurrenceLiteralField, hzero])
      hliteral]
    rw [show 7 = 6 + 1 by omega]
    rw [run_branchZero_instruction (by rfl) rfl]
    rw [ite_self]
    exact run_literalPrepFinish _ (occurrenceLiteralField clauseCode position)
      position systematicBits assignmentBits inputArity encoded inputCode _
      rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
      hframeOne hframeTwo hassignment hdecode houtput

/-! ### 3.5 Dispatch tag and branch payload -/

/-!
Register ABI: `r2` decoded literal, `r3` context, `r4` complement tag, `r5`
assignment index, `r6`–`r9` context tails, `r10` dispatch tag, `r11` branch
context, `r12` branch payload.
-/
def branchPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 2 4 3
  , .unpairRight 2 5 4
  , .unpairRight 3 6 5
  , .unpairLeft 6 7 6
  , .unpairRight 6 8 7
  , .unpairRight 8 9 8
  , .subtract 7 5 10 9
  , .pair 7 9 11 10
  , .pair 4 11 11 11
  , .pair 5 11 12 12
  , .pair 10 12 0 13
  , .halt 0
  ]

@[simp] theorem branchPrepProgram_oracleFree :
    OracleFree branchPrepProgram := by
  rfl

def branchPrepFuel : ℕ := 14

def branchPrepOutput
    (tag index systematicBits inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair (systematicBits - index)
    (Nat.pair index
      (occurrenceContextTwo tag systematicBits inputArity encoded inputCode))

def branchPrepBits
    (tag index position systematicBits assignmentBits inputArity encoded
      inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair (Nat.pair tag index)
        (occurrenceContextOne position systematicBits assignmentBits
          inputArity encoded inputCode))
      (branchPrepOutput tag index systematicBits inputArity encoded
        inputCode))

theorem run_branchPrepProgram
    (inputLength tag index position systematicBits assignmentBits inputArity
      encoded inputCode : ℕ) :
    runNPOracleProgram branchPrepProgram
        (branchPrepBits tag index position systematicBits assignmentBits
          inputArity encoded inputCode)
        branchPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair tag index)
            (occurrenceContextOne position systematicBits assignmentBits
              inputArity encoded inputCode))) =
      some
        (branchPrepOutput tag index systematicBits inputArity encoded
          inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair (Nat.pair tag index)
          (occurrenceContextOne position systematicBits assignmentBits
            inputArity encoded inputCode) →
      natBitLength value ≤
        branchPrepBits tag index position systematicBits assignmentBits
          inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        branchPrepOutput tag index systematicBits inputArity encoded
          inputCode →
      natBitLength value ≤
        branchPrepBits tag index position systematicBits assignmentBits
          inputArity encoded inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hsystematicLe :
      systematicBits ≤
        Nat.pair (Nat.pair tag index)
          (occurrenceContextOne position systematicBits assignmentBits
            inputArity encoded inputCode) :=
    le_pair_of_le_right
      (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hdecoded :=
    hrequest (Nat.pair tag index) (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest
      (occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have htag :=
    hrequest tag (le_pair_of_le_left (le_pair_of_le_left (le_refl _)))
  have hindex :=
    hrequest index (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hframeOne :=
    hrequest
      (Nat.pair systematicBits
        (Nat.pair assignmentBits
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hsystematic := hrequest systematicBits hsystematicLe
  have hframeTwo :=
    hrequest
      (Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hframeThree :=
    hrequest (Nat.pair inputArity (Nat.pair encoded inputCode))
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have hdispatch :=
    hrequest (systematicBits - index) ((Nat.sub_le _ _).trans hsystematicLe)
  have hbranchFrame :=
    hresult
      (Nat.pair systematicBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hbranchContext :=
    hresult
      (occurrenceContextTwo tag systematicBits inputArity encoded inputCode)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hpayload :=
    hresult
      (Nat.pair index
        (occurrenceContextTwo tag systematicBits inputArity encoded inputCode))
      (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show branchPrepFuel = 13 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := Nat.pair tag index)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hdecoded]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      occurrenceContextOne position systematicBits assignmentBits inputArity
        encoded inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htag]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindex]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair systematicBits
        (Nat.pair assignmentBits
          (Nat.pair inputArity (Nat.pair encoded inputCode))))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextOne])
    hframeOne]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairLeft_instruction (value := systematicBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsystematic]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair assignmentBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair inputArity (Nat.pair encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeThree]
  rw [show 6 = 5 + 1 by omega]
  rw [run_subtract_instruction (value := systematicBits - index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdispatch]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair systematicBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hbranchFrame]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      occurrenceContextTwo tag systematicBits inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextTwo])
    hbranchContext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair index
        (occurrenceContextTwo tag systematicBits inputArity encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      branchPrepOutput tag index systematicBits inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, branchPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.6 Preparing the systematic support call -/

/-!
Register ABI: `r2` index, `r3` context, `r4` complement tag, `r5`–`r6` context
tails, `r7` arity, `r8` circuit-and-code pair, `r9` encoded circuit, `r10`
occurrence code, `r11` native request, `r12` parity context.
-/
def supportPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairRight 5 6 5
  , .unpairLeft 6 7 6
  , .unpairRight 6 8 7
  , .unpairLeft 8 9 8
  , .unpairRight 8 10 9
  , .pair 9 2 11 10
  , .pair 7 11 11 11
  , .pair 7 10 12 12
  , .pair 4 12 12 13
  , .pair 11 12 0 14
  , .halt 0
  ]

@[simp] theorem supportPrepProgram_oracleFree :
    OracleFree supportPrepProgram := by
  rfl

def supportPrepFuel : ℕ := 15

def supportPrepOutput (index tag inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair (nativeInputRequest inputArity (Nat.pair encoded index))
    (occurrenceContextThree tag inputArity inputCode)

def supportPrepBits
    (index tag systematicBits inputArity encoded inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair index
        (occurrenceContextTwo tag systematicBits inputArity encoded inputCode))
      (supportPrepOutput index tag inputArity encoded inputCode))

theorem run_supportPrepProgram
    (inputLength index tag systematicBits inputArity encoded inputCode : ℕ) :
    runNPOracleProgram supportPrepProgram
        (supportPrepBits index tag systematicBits inputArity encoded inputCode)
        supportPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair index
            (occurrenceContextTwo tag systematicBits inputArity encoded
              inputCode))) =
      some
        (supportPrepOutput index tag inputArity encoded inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair index
          (occurrenceContextTwo tag systematicBits inputArity encoded
            inputCode) →
      natBitLength value ≤
        supportPrepBits index tag systematicBits inputArity encoded
          inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ supportPrepOutput index tag inputArity encoded inputCode →
      natBitLength value ≤
        supportPrepBits index tag systematicBits inputArity encoded
          inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hindex := hrequest index (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest
      (occurrenceContextTwo tag systematicBits inputArity encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have htag :=
    hrequest tag (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hframeOne :=
    hrequest
      (Nat.pair systematicBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hframeTwo :=
    hrequest (Nat.pair inputArity (Nat.pair encoded inputCode))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have harity :=
    hrequest inputArity
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))))
  have hpairCode :=
    hrequest (Nat.pair encoded inputCode)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have hencoded :=
    hrequest encoded
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))))
  have hinputCode :=
    hrequest inputCode
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))))
  have hcodePair :=
    hresult (Nat.pair encoded index)
      (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hnative :=
    hresult (nativeInputRequest inputArity (Nat.pair encoded index))
      (le_pair_of_le_left (le_refl _))
  have hparityFrame :=
    hresult (Nat.pair inputArity inputCode)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hparityContext :=
    hresult (occurrenceContextThree tag inputArity inputCode)
      (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show supportPrepFuel = 14 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hindex]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      occurrenceContextTwo tag systematicBits inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextTwo])
    htag]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair systematicBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextTwo])
    hframeOne]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair inputArity (Nat.pair encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpairCode]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hencoded]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCode]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair encoded index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcodePair]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := nativeInputRequest inputArity (Nat.pair encoded index))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeInputRequest])
    hnative]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputArity inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hparityFrame]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := occurrenceContextThree tag inputArity inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextThree])
    hparityContext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      supportPrepOutput index tag inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, supportPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.7 Preparing the masked parity fold -/

/-!
Register ABI: `r2` support word, `r3` context, `r4` complement tag, `r5`
arity-and-code pair, `r6` arity, `r7` occurrence code, `r8` range request.
-/
def parityPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .pair 2 7 8 7
  , .pair 6 8 8 8
  , .pair 8 4 0 9
  , .halt 0
  ]

@[simp] theorem parityPrepProgram_oracleFree :
    OracleFree parityPrepProgram := by
  rfl

def parityPrepFuel : ℕ := 10

def parityPrepOutput
    (supportCode tag inputArity inputCode : ℕ) : ℕ :=
  Nat.pair
    (generatedBalancedRangeInput inputArity
      (maskContext supportCode inputCode))
    tag

def parityPrepBits
    (supportCode tag inputArity inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair supportCode (occurrenceContextThree tag inputArity inputCode))
      (parityPrepOutput supportCode tag inputArity inputCode))

theorem run_parityPrepProgram
    (inputLength supportCode tag inputArity inputCode : ℕ) :
    runNPOracleProgram parityPrepProgram
        (parityPrepBits supportCode tag inputArity inputCode)
        parityPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair supportCode
            (occurrenceContextThree tag inputArity inputCode))) =
      some (parityPrepOutput supportCode tag inputArity inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair supportCode
          (occurrenceContextThree tag inputArity inputCode) →
      natBitLength value ≤
        parityPrepBits supportCode tag inputArity inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ parityPrepOutput supportCode tag inputArity inputCode →
      natBitLength value ≤
        parityPrepBits supportCode tag inputArity inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hsupport := hrequest supportCode (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest (occurrenceContextThree tag inputArity inputCode)
      (le_pair_of_le_right (le_refl _))
  have htag :=
    hrequest tag (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hframe :=
    hrequest (Nat.pair inputArity inputCode)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have harity :=
    hrequest inputArity
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hinputCode :=
    hrequest inputCode
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hmask :=
    hresult (maskContext supportCode inputCode)
      (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hrange :=
    hresult
      (generatedBalancedRangeInput inputArity
        (maskContext supportCode inputCode))
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show parityPrepFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := supportCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hsupport]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := occurrenceContextThree tag inputArity inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextThree])
    htag]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair inputArity inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextThree])
    hframe]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCode]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := maskContext supportCode inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, maskContext])
    hmask]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      generatedBalancedRangeInput inputArity
        (maskContext supportCode inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      generatedBalancedRangeInput])
    hrange]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := parityPrepOutput supportCode tag inputArity inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, parityPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.8 Preparing the auxiliary honest call

The honest runner consumes the canonical code of its own input arity, which
is exactly the zero-offset digit window of the public occurrence code.  The
adapter therefore emits one `bitSliceProgram` request and keeps the auxiliary
index beside it. -/

/-!
Register ABI: `r2` index, `r3` context, `r4` complement tag, `r5` context
tail, `r6` systematic width, `r7` arity-and-circuit frame, `r8` arity, `r9`
circuit-and-code pair, `r10` encoded circuit, `r11` occurrence code, `r12`
honest context, `r13` window offset, `r14` slice request.
-/
def honestSlicePrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 9 10 9
  , .unpairRight 9 11 10
  , .pair 8 10 12 11
  , .pair 2 12 12 12
  , .pair 6 12 12 13
  , .pair 4 12 12 14
  , .set 13 0 15
  , .pair 8 11 14 16
  , .pair 13 14 14 17
  , .pair 14 12 0 18
  , .halt 0
  ]

@[simp] theorem honestSlicePrepProgram_oracleFree :
    OracleFree honestSlicePrepProgram := by
  rfl

def honestSlicePrepFuel : ℕ := 19

def honestSlicePrepOutput
    (index tag systematicBits inputArity encoded inputCode : ℕ) : ℕ :=
  Nat.pair (bitSliceInput 0 inputArity inputCode)
    (occurrenceContextFour tag systematicBits index inputArity encoded)

def honestSlicePrepBits
    (index tag systematicBits inputArity encoded inputCode : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair index
        (occurrenceContextTwo tag systematicBits inputArity encoded inputCode))
      (honestSlicePrepOutput index tag systematicBits inputArity encoded
        inputCode))

theorem run_honestSlicePrepProgram
    (inputLength index tag systematicBits inputArity encoded inputCode : ℕ) :
    runNPOracleProgram honestSlicePrepProgram
        (honestSlicePrepBits index tag systematicBits inputArity encoded
          inputCode)
        honestSlicePrepFuel
        (initialNPOracleState inputLength
          (Nat.pair index
            (occurrenceContextTwo tag systematicBits inputArity encoded
              inputCode))) =
      some
        (honestSlicePrepOutput index tag systematicBits inputArity encoded
          inputCode) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair index
          (occurrenceContextTwo tag systematicBits inputArity encoded
            inputCode) →
      natBitLength value ≤
        honestSlicePrepBits index tag systematicBits inputArity encoded
          inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        honestSlicePrepOutput index tag systematicBits inputArity encoded
          inputCode →
      natBitLength value ≤
        honestSlicePrepBits index tag systematicBits inputArity encoded
          inputCode :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hindex := hrequest index (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest
      (occurrenceContextTwo tag systematicBits inputArity encoded inputCode)
      (le_pair_of_le_right (le_refl _))
  have htag :=
    hrequest tag (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hframeOne :=
    hrequest
      (Nat.pair systematicBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hsystematic :=
    hrequest systematicBits
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hframeTwo :=
    hrequest (Nat.pair inputArity (Nat.pair encoded inputCode))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have harity :=
    hrequest inputArity
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))))
  have hpairCode :=
    hrequest (Nat.pair encoded inputCode)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have hencoded :=
    hrequest encoded
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))))
  have hinputCode :=
    hrequest inputCode
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))))
  have hzero := hrequest 0 (Nat.zero_le _)
  have hhonestFrameOne :=
    hresult (Nat.pair inputArity encoded)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have hhonestFrameTwo :=
    hresult (Nat.pair index (Nat.pair inputArity encoded))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hhonestFrameThree :=
    hresult
      (Nat.pair systematicBits (Nat.pair index (Nat.pair inputArity encoded)))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hhonestContext :=
    hresult
      (occurrenceContextFour tag systematicBits index inputArity encoded)
      (le_pair_of_le_right (le_refl _))
  have hwindow :=
    hresult (Nat.pair inputArity inputCode)
      (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hslice :=
    hresult (bitSliceInput 0 inputArity inputCode)
      (le_pair_of_le_left (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show honestSlicePrepFuel = 18 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hindex]
  rw [show 18 = 17 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      occurrenceContextTwo tag systematicBits inputArity encoded inputCode)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 17 = 16 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextTwo])
    htag]
  rw [show 16 = 15 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair systematicBits
        (Nat.pair inputArity (Nat.pair encoded inputCode)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, occurrenceContextTwo])
    hframeOne]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairLeft_instruction (value := systematicBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsystematic]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair inputArity (Nat.pair encoded inputCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair encoded inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hpairCode]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hencoded]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hinputCode]
  rw [show 9 = 8 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputArity encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hhonestFrameOne]
  rw [show 8 = 7 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair index (Nat.pair inputArity encoded))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hhonestFrameTwo]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair systematicBits (Nat.pair index (Nat.pair inputArity encoded)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hhonestFrameThree]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      occurrenceContextFour tag systematicBits index inputArity encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextFour])
    hhonestContext]
  rw [show 5 = 4 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputArity inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hwindow]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := bitSliceInput 0 inputArity inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, bitSliceInput])
    hslice]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      honestSlicePrepOutput index tag systematicBits inputArity encoded
        inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      honestSlicePrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.9 Framing the honest call itself -/

/-!
Register ABI: `r2` prefix code, `r3` context, `r4` complement tag, `r5`
context tail, `r6` systematic width, `r7` index frame, `r8` index, `r9`
arity-and-circuit pair, `r10` arity, `r11` encoded circuit, `r12` native
request, `r13` digit context.
-/
def honestPrepProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .unpairLeft 7 8 7
  , .unpairRight 7 9 8
  , .unpairLeft 9 10 9
  , .unpairRight 9 11 10
  , .pair 11 2 12 11
  , .pair 10 12 12 12
  , .pair 6 8 13 13
  , .pair 4 13 13 14
  , .pair 12 13 0 15
  , .halt 0
  ]

@[simp] theorem honestPrepProgram_oracleFree :
    OracleFree honestPrepProgram := by
  rfl

def honestPrepFuel : ℕ := 16

def honestPrepOutput
    (prefixCode tag systematicBits index inputArity encoded : ℕ) : ℕ :=
  Nat.pair (nativeInputRequest inputArity (Nat.pair encoded prefixCode))
    (occurrenceContextFive tag systematicBits index)

def honestPrepBits
    (prefixCode tag systematicBits index inputArity encoded : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair prefixCode
        (occurrenceContextFour tag systematicBits index inputArity encoded))
      (honestPrepOutput prefixCode tag systematicBits index inputArity
        encoded))

theorem run_honestPrepProgram
    (inputLength prefixCode tag systematicBits index inputArity
      encoded : ℕ) :
    runNPOracleProgram honestPrepProgram
        (honestPrepBits prefixCode tag systematicBits index inputArity encoded)
        honestPrepFuel
        (initialNPOracleState inputLength
          (Nat.pair prefixCode
            (occurrenceContextFour tag systematicBits index inputArity
              encoded))) =
      some
        (honestPrepOutput prefixCode tag systematicBits index inputArity
          encoded) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair prefixCode
          (occurrenceContextFour tag systematicBits index inputArity
            encoded) →
      natBitLength value ≤
        honestPrepBits prefixCode tag systematicBits index inputArity
          encoded :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤
        honestPrepOutput prefixCode tag systematicBits index inputArity
          encoded →
      natBitLength value ≤
        honestPrepBits prefixCode tag systematicBits index inputArity
          encoded :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hprefix := hrequest prefixCode (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest
      (occurrenceContextFour tag systematicBits index inputArity encoded)
      (le_pair_of_le_right (le_refl _))
  have htag :=
    hrequest tag (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hframeOne :=
    hrequest
      (Nat.pair systematicBits (Nat.pair index (Nat.pair inputArity encoded)))
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hsystematic :=
    hrequest systematicBits
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hframeTwo :=
    hrequest (Nat.pair index (Nat.pair inputArity encoded))
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))
  have hindex :=
    hrequest index
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))))
  have hframeThree :=
    hrequest (Nat.pair inputArity encoded)
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))))
  have harity :=
    hrequest inputArity
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))))
  have hencoded :=
    hrequest encoded
      (le_pair_of_le_right
        (le_pair_of_le_right
          (le_pair_of_le_right
            (le_pair_of_le_right (le_pair_of_le_right (le_refl _))))))
  have hcodePair :=
    hresult (Nat.pair encoded prefixCode)
      (le_pair_of_le_left (le_pair_of_le_right (le_refl _)))
  have hnative :=
    hresult (nativeInputRequest inputArity (Nat.pair encoded prefixCode))
      (le_pair_of_le_left (le_refl _))
  have hdigitFrame :=
    hresult (Nat.pair systematicBits index)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hdigitContext :=
    hresult (occurrenceContextFive tag systematicBits index)
      (le_pair_of_le_right (le_refl _))
  have houtput := hresult _ (le_refl _)
  rw [show honestPrepFuel = 15 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := prefixCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hprefix]
  rw [show 15 = 14 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      occurrenceContextFour tag systematicBits index inputArity encoded)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextFour])
    htag]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair systematicBits (Nat.pair index (Nat.pair inputArity encoded)))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextFour])
    hframeOne]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := systematicBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsystematic]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair index (Nat.pair inputArity encoded))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeTwo]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindex]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair inputArity encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hframeThree]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := inputArity)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harity]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hencoded]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair encoded prefixCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hcodePair]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction
    (value := nativeInputRequest inputArity (Nat.pair encoded prefixCode))
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, nativeInputRequest])
    hnative]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair systematicBits index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdigitFrame]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction
    (value := occurrenceContextFive tag systematicBits index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextFive])
    hdigitContext]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      honestPrepOutput prefixCode tag systematicBits index inputArity encoded)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, honestPrepOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.10 Reading the auxiliary digit -/

/-!
Register ABI: `r2` honest word, `r3` context, `r4` complement tag, `r5`
width-and-index pair, `r6` systematic width, `r7` index, `r8` auxiliary
offset, `r9` assignment digit.
-/
def auxiliaryFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .unpairLeft 5 6 5
  , .unpairRight 5 7 6
  , .subtract 7 6 8 7
  , .testBit 2 8 9 8
  , .pair 9 4 0 9
  , .halt 0
  ]

@[simp] theorem auxiliaryFinishProgram_oracleFree :
    OracleFree auxiliaryFinishProgram := by
  rfl

def auxiliaryFinishFuel : ℕ := 10

def auxiliaryFinishOutput
    (honestCode tag systematicBits index : ℕ) : ℕ :=
  Nat.pair (honestCode.testBit (index - systematicBits)).toNat tag

def auxiliaryFinishBits
    (honestCode tag systematicBits index : ℕ) : ℕ :=
  natBitLength
    (max
      (Nat.pair honestCode (occurrenceContextFive tag systematicBits index))
      (auxiliaryFinishOutput honestCode tag systematicBits index))

theorem run_auxiliaryFinishProgram
    (inputLength honestCode tag systematicBits index : ℕ) :
    runNPOracleProgram auxiliaryFinishProgram
        (auxiliaryFinishBits honestCode tag systematicBits index)
        auxiliaryFinishFuel
        (initialNPOracleState inputLength
          (Nat.pair honestCode
            (occurrenceContextFive tag systematicBits index))) =
      some (auxiliaryFinishOutput honestCode tag systematicBits index) := by
  have hrequest : ∀ value : ℕ,
      value ≤
        Nat.pair honestCode
          (occurrenceContextFive tag systematicBits index) →
      natBitLength value ≤
        auxiliaryFinishBits honestCode tag systematicBits index :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hresult : ∀ value : ℕ,
      value ≤ auxiliaryFinishOutput honestCode tag systematicBits index →
      natBitLength value ≤
        auxiliaryFinishBits honestCode tag systematicBits index :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_right _ _))
  have hindexLe :
      index ≤
        Nat.pair honestCode
          (occurrenceContextFive tag systematicBits index) :=
    le_pair_of_le_right (le_pair_of_le_right (le_pair_of_le_right
      (le_refl _)))
  have hhonest := hrequest honestCode (le_pair_of_le_left (le_refl _))
  have hcontext :=
    hrequest (occurrenceContextFive tag systematicBits index)
      (le_pair_of_le_right (le_refl _))
  have htag :=
    hrequest tag (le_pair_of_le_right (le_pair_of_le_left (le_refl _)))
  have hframe :=
    hrequest (Nat.pair systematicBits index)
      (le_pair_of_le_right (le_pair_of_le_right (le_refl _)))
  have hsystematic :=
    hrequest systematicBits
      (le_pair_of_le_right
        (le_pair_of_le_right (le_pair_of_le_left (le_refl _))))
  have hindex := hrequest index hindexLe
  have hoffset :=
    hrequest (index - systematicBits) ((Nat.sub_le _ _).trans hindexLe)
  have hdigit :
      natBitLength (honestCode.testBit (index - systematicBits)).toNat ≤
        auxiliaryFinishBits honestCode tag systematicBits index :=
    digit_bits (toNat_le_one _)
  have houtput := hresult _ (le_refl _)
  rw [show auxiliaryFinishFuel = 9 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := honestCode)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hhonest]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := occurrenceContextFive tag systematicBits index)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcontext]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextFive])
    htag]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair systematicBits index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      occurrenceContextFive])
    hframe]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (value := systematicBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsystematic]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hindex]
  rw [show 4 = 3 + 1 by omega]
  rw [run_subtract_instruction (value := index - systematicBits)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hoffset]
  rw [show 3 = 2 + 1 by omega]
  rw [run_testBit_instruction
    (value := (honestCode.testBit (index - systematicBits)).toNat)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdigit]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction
    (value := auxiliaryFinishOutput honestCode tag systematicBits index)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump,
      auxiliaryFinishOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    houtput

/-! ### 3.11 The complementing exclusive-or suffix -/

/-!
Register ABI: `r2` assignment digit, `r3` complement digit, `r4` sum, `r5`
constant zero.  Adding two digits and reading digit zero of the sum is
exclusive-or.
-/
def xorFinishProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .add 2 3 4 3
  , .set 5 0 4
  , .testBit 4 5 0 5
  , .halt 0
  ]

@[simp] theorem xorFinishProgram_oracleFree :
    OracleFree xorFinishProgram := by
  rfl

def xorFinishFuel : ℕ := 6

def xorFinishBits (left right : ℕ) : ℕ :=
  natBitLength (max (Nat.pair left right) (left + right))

theorem run_xorFinishProgram (inputLength left right : ℕ) :
    runNPOracleProgram xorFinishProgram (xorFinishBits left right)
        xorFinishFuel
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some ((left + right).testBit 0).toNat := by
  have hrequest : ∀ value : ℕ, value ≤ Nat.pair left right →
      natBitLength value ≤ xorFinishBits left right :=
    fun _ hvalue => natBitLength_mono (hvalue.trans (Nat.le_max_left _ _))
  have hleft := hrequest left (le_pair_of_le_left (le_refl _))
  have hright := hrequest right (le_pair_of_le_right (le_refl _))
  have hzero := hrequest 0 (Nat.zero_le _)
  have hsum : natBitLength (left + right) ≤ xorFinishBits left right :=
    natBitLength_mono (Nat.le_max_right _ _)
  have hdigit :
      natBitLength ((left + right).testBit 0).toNat ≤
        xorFinishBits left right :=
    digit_bits (toNat_le_one _)
  rw [show xorFinishFuel = 5 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleft]
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairRight_instruction (value := right)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hright]
  rw [show 4 = 3 + 1 by omega]
  rw [run_add_instruction (value := left + right)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hsum]
  rw [show 3 = 2 + 1 by omega]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzero]
  rw [show 2 = 1 + 1 by omega]
  rw [run_testBit_instruction (value := ((left + right).testBit 0).toNat)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdigit]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hdigit

/-- Adding two digits and reading digit zero is exclusive-or. -/
theorem testBit_zero_toNat_add (left right : Bool) :
    ((left.toNat + right.toNat).testBit 0).toNat = (xor left right).toNat := by
  cases left <;> cases right <;> decide

/-! ## 4. Linking at one charged width

Every composition below is one application of `run_occurrenceStage`, so no
width comparison in this module is deeper than two `max` levels. -/

/-- Width of one linked stage: the public length, the leading program's own
width, and the width of everything that follows it. -/
def occurrenceStageBits (outerInputLength headBits tailBits : ℕ) : ℕ :=
  max (natBitLength outerInputLength) (max headBits tailBits)

/-- One verified link charged at the stage width above. -/
theorem run_occurrenceStage {first second : NPOracleProgram}
    {outerInputLength headBits tailBits firstFuel secondFuel inputCode
      intermediate output : ℕ}
    (hfirst :
      runNPOracleProgram first headBits firstFuel
        (initialNPOracleState outerInputLength inputCode) = some intermediate)
    (hsecond :
      runNPOracleProgram second tailBits secondFuel
        (initialNPOracleState outerInputLength intermediate) = some output) :
    runNPOracleProgram (linkPrograms first second)
        (occurrenceStageBits outerInputLength headBits tailBits)
        (linkFuel second firstFuel secondFuel)
        (initialNPOracleState outerInputLength inputCode) =
      some output := by
  have hlength :
      natBitLength outerInputLength ≤
        occurrenceStageBits outerInputLength headBits tailBits :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ occurrenceStageBits outerInputLength headBits tailBits := by
    exact (show 1 ≤ natBitLength outerInputLength by
      unfold natBitLength
      omega).trans hlength
  exact run_linkPrograms hpositive hlength
    (run_bits_mono hfirst
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
    (run_bits_mono hsecond
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))

/-- The zero-offset digit window is the canonical low-bit projection. -/
theorem bitSlice_zero_eq_bitInputPrefix (width value : ℕ) :
    bitSlice 0 width value = bitInputPrefix width value :=
  rfl

/-! ## 5. The systematic assignment branch

One support-runner call at the selected index, followed by the fixed masked
parity controller of `CaseTwoOccurrenceParityProgram`. -/

def caseTwoSystematicBranchProgram
    (factory : ExecutablePointwisePCPPFactory) : NPOracleProgram :=
  linkPrograms supportPrepProgram <|
    linkPrograms (preserveRightProgram (supportCallProgram factory)) <|
      linkPrograms parityPrepProgram
        (preserveRightProgram maskedParityProgram)

theorem caseTwoSystematicBranchProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (caseTwoSystematicBranchProgram factory) := by
  apply oracleFree_linkPrograms supportPrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree (supportCallProgram factory)
      (supportCallProgram_oracleFree factory)
  · apply oracleFree_linkPrograms parityPrepProgram_oracleFree
    exact preserveRightProgram_oracleFree maskedParityProgram
      maskedParityProgram_oracleFree

def caseTwoSystematicBranchFuel
    (factory : ExecutablePointwisePCPPFactory) (outerInputLength : ℕ)
    {n : ℕ} (circuit : BooleanCircuit n) (index inputCode : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram (supportCallProgram factory))
      (linkPrograms parityPrepProgram
        (preserveRightProgram maskedParityProgram)))
    supportPrepFuel <|
    linkFuel
      (linkPrograms parityPrepProgram
        (preserveRightProgram maskedParityProgram))
      (preserveRightFuel (supportCallFuel factory circuit index)) <|
      linkFuel (preserveRightProgram maskedParityProgram) parityPrepFuel
        (preserveRightFuel
          (maskedParityFuel outerInputLength n
            (occurrenceSupportCode factory circuit index) inputCode))

def caseTwoSystematicBranchBits
    (factory : ExecutablePointwisePCPPFactory) (outerInputLength : ℕ)
    {n : ℕ} (circuit : BooleanCircuit n)
    (index complement systematicBits inputCode : ℕ) : ℕ :=
  occurrenceStageBits outerInputLength
    (supportPrepBits index complement systematicBits n
      (encodeBooleanCircuit circuit) inputCode) <|
    occurrenceStageBits outerInputLength
      (preserveRightBits
        (supportCallBits factory outerInputLength circuit index)
        (nativeInputRequest n (supportRequestCode circuit index))
        (occurrenceContextThree complement n inputCode)
        (occurrenceSupportCode factory circuit index)) <|
      occurrenceStageBits outerInputLength
        (parityPrepBits (occurrenceSupportCode factory circuit index)
          complement n inputCode)
        (preserveRightBits
          (maskedParityBits outerInputLength n
            (occurrenceSupportCode factory circuit index) inputCode)
          (generatedBalancedRangeInput n
            (maskContext (occurrenceSupportCode factory circuit index)
              inputCode))
          complement
          ((supportMaskBits (occurrenceSupportCode factory circuit index)
            (bitInputPrefixView n inputCode)).foldl xor false).toNat)

/-- Exact execution of the systematic branch: the masked support parity of the
selected index, beside the retained complement digit. -/
theorem run_caseTwoSystematicBranchProgram
    (factory : ExecutablePointwisePCPPFactory) (outerInputLength : ℕ)
    {n : ℕ} (circuit : BooleanCircuit n)
    (index complement systematicBits inputCode : ℕ) :
    runNPOracleProgram (caseTwoSystematicBranchProgram factory)
        (caseTwoSystematicBranchBits factory outerInputLength circuit index
          complement systematicBits inputCode)
        (caseTwoSystematicBranchFuel factory outerInputLength circuit index
          inputCode)
        (initialNPOracleState outerInputLength
          (Nat.pair index
            (occurrenceContextTwo complement systematicBits n
              (encodeBooleanCircuit circuit) inputCode))) =
      some
        (Nat.pair
          ((supportMaskBits (occurrenceSupportCode factory circuit index)
            (bitInputPrefixView n inputCode)).foldl xor false).toNat
          complement) := by
  have hsupportCall :
      runNPOracleProgram (preserveRightProgram (supportCallProgram factory))
          (preserveRightBits
            (supportCallBits factory outerInputLength circuit index)
            (nativeInputRequest n (supportRequestCode circuit index))
            (occurrenceContextThree complement n inputCode)
            (occurrenceSupportCode factory circuit index))
          (preserveRightFuel (supportCallFuel factory circuit index))
          (initialNPOracleState outerInputLength
            (Nat.pair (nativeInputRequest n (supportRequestCode circuit index))
              (occurrenceContextThree complement n inputCode))) =
        some
          (Nat.pair (occurrenceSupportCode factory circuit index)
            (occurrenceContextThree complement n inputCode)) :=
    run_preserveRightProgram (supportCallProgram factory) outerInputLength
      (supportCallBits factory outerInputLength circuit index)
      (supportCallFuel factory circuit index)
      (nativeInputRequest n (supportRequestCode circuit index))
      (occurrenceContextThree complement n inputCode)
      (occurrenceSupportCode factory circuit index)
      (run_supportCallProgram factory outerInputLength circuit index)
  have hparity :
      runNPOracleProgram (preserveRightProgram maskedParityProgram)
          (preserveRightBits
            (maskedParityBits outerInputLength n
              (occurrenceSupportCode factory circuit index) inputCode)
            (generatedBalancedRangeInput n
              (maskContext (occurrenceSupportCode factory circuit index)
                inputCode))
            complement
            ((supportMaskBits (occurrenceSupportCode factory circuit index)
              (bitInputPrefixView n inputCode)).foldl xor false).toNat)
          (preserveRightFuel
            (maskedParityFuel outerInputLength n
              (occurrenceSupportCode factory circuit index) inputCode))
          (initialNPOracleState outerInputLength
            (Nat.pair
              (generatedBalancedRangeInput n
                (maskContext (occurrenceSupportCode factory circuit index)
                  inputCode))
              complement)) =
        some
          (Nat.pair
            ((supportMaskBits (occurrenceSupportCode factory circuit index)
              (bitInputPrefixView n inputCode)).foldl xor false).toNat
            complement) :=
    run_preserveRightProgram maskedParityProgram outerInputLength
      (maskedParityBits outerInputLength n
        (occurrenceSupportCode factory circuit index) inputCode)
      (maskedParityFuel outerInputLength n
        (occurrenceSupportCode factory circuit index) inputCode)
      (generatedBalancedRangeInput n
        (maskContext (occurrenceSupportCode factory circuit index) inputCode))
      complement
      ((supportMaskBits (occurrenceSupportCode factory circuit index)
        (bitInputPrefixView n inputCode)).foldl xor false).toNat
      (run_maskedParityProgram outerInputLength n
        (occurrenceSupportCode factory circuit index) inputCode)
  exact run_occurrenceStage
    (run_supportPrepProgram outerInputLength index complement systematicBits n
      (encodeBooleanCircuit circuit) inputCode)
    (run_occurrenceStage hsupportCall
      (run_occurrenceStage
        (run_parityPrepProgram outerInputLength
          (occurrenceSupportCode factory circuit index) complement n inputCode)
        hparity))

/-! ## 6. The auxiliary assignment branch

One honest-runner call on the low digit window of the occurrence code,
followed by a single digit read at the auxiliary offset. -/

def caseTwoAuxiliaryBranchProgram
    (factory : ExecutablePointwisePCPPFactory) : NPOracleProgram :=
  linkPrograms honestSlicePrepProgram <|
    linkPrograms (preserveRightProgram bitSliceProgram) <|
      linkPrograms honestPrepProgram <|
        linkPrograms (preserveRightProgram (honestCallProgram factory))
          auxiliaryFinishProgram

theorem caseTwoAuxiliaryBranchProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (caseTwoAuxiliaryBranchProgram factory) := by
  apply oracleFree_linkPrograms honestSlicePrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree bitSliceProgram
      bitSliceProgram_oracleFree
  · apply oracleFree_linkPrograms honestPrepProgram_oracleFree
    apply oracleFree_linkPrograms
    · exact preserveRightProgram_oracleFree (honestCallProgram factory)
        (honestCallProgram_oracleFree factory)
    · exact auxiliaryFinishProgram_oracleFree

def caseTwoAuxiliaryBranchFuel
    (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram bitSliceProgram)
      (linkPrograms honestPrepProgram
        (linkPrograms (preserveRightProgram (honestCallProgram factory))
          auxiliaryFinishProgram)))
    honestSlicePrepFuel <|
    linkFuel
      (linkPrograms honestPrepProgram
        (linkPrograms (preserveRightProgram (honestCallProgram factory))
          auxiliaryFinishProgram))
      (preserveRightFuel (bitSliceFuel n)) <|
      linkFuel
        (linkPrograms (preserveRightProgram (honestCallProgram factory))
          auxiliaryFinishProgram)
        honestPrepFuel <|
        linkFuel auxiliaryFinishProgram
          (preserveRightFuel (honestCallFuel factory circuit inputCode))
          auxiliaryFinishFuel

def caseTwoAuxiliaryBranchBits
    (factory : ExecutablePointwisePCPPFactory) (outerInputLength : ℕ)
    {n : ℕ} (circuit : BooleanCircuit n)
    (index complement systematicBits inputCode : ℕ) : ℕ :=
  occurrenceStageBits outerInputLength
    (honestSlicePrepBits index complement systematicBits n
      (encodeBooleanCircuit circuit) inputCode) <|
    occurrenceStageBits outerInputLength
      (preserveRightBits (bitSliceBits outerInputLength 0 n inputCode)
        (bitSliceInput 0 n inputCode)
        (occurrenceContextFour complement systematicBits index n
          (encodeBooleanCircuit circuit))
        (bitInputPrefix n inputCode)) <|
      occurrenceStageBits outerInputLength
        (honestPrepBits (bitInputPrefix n inputCode) complement systematicBits
          index n (encodeBooleanCircuit circuit)) <|
        occurrenceStageBits outerInputLength
          (preserveRightBits
            (honestCallBits factory outerInputLength circuit inputCode)
            (nativeInputRequest n (honestRequestCode circuit inputCode))
            (occurrenceContextFive complement systematicBits index)
            (occurrenceHonestCode factory circuit
              (bitInputPrefixView n inputCode)))
          (auxiliaryFinishBits
            (occurrenceHonestCode factory circuit
              (bitInputPrefixView n inputCode))
            complement systematicBits index)

/-- Exact execution of the auxiliary branch: one digit of the honest word at
the auxiliary offset, beside the retained complement digit. -/
theorem run_caseTwoAuxiliaryBranchProgram
    (factory : ExecutablePointwisePCPPFactory) (outerInputLength : ℕ)
    {n : ℕ} (circuit : BooleanCircuit n)
    (index complement systematicBits inputCode : ℕ) :
    runNPOracleProgram (caseTwoAuxiliaryBranchProgram factory)
        (caseTwoAuxiliaryBranchBits factory outerInputLength circuit index
          complement systematicBits inputCode)
        (caseTwoAuxiliaryBranchFuel factory circuit inputCode)
        (initialNPOracleState outerInputLength
          (Nat.pair index
            (occurrenceContextTwo complement systematicBits n
              (encodeBooleanCircuit circuit) inputCode))) =
      some
        (Nat.pair
          ((occurrenceHonestCode factory circuit
            (bitInputPrefixView n inputCode)).testBit
              (index - systematicBits)).toNat
          complement) := by
  have hwindow :
      runNPOracleProgram bitSliceProgram
          (bitSliceBits outerInputLength 0 n inputCode) (bitSliceFuel n)
          (initialNPOracleState outerInputLength
            (bitSliceInput 0 n inputCode)) =
        some (bitInputPrefix n inputCode) := by
    rw [← bitSlice_zero_eq_bitInputPrefix n inputCode]
    exact run_bitSliceProgram outerInputLength 0 n inputCode
  have hslice :
      runNPOracleProgram (preserveRightProgram bitSliceProgram)
          (preserveRightBits (bitSliceBits outerInputLength 0 n inputCode)
            (bitSliceInput 0 n inputCode)
            (occurrenceContextFour complement systematicBits index n
              (encodeBooleanCircuit circuit))
            (bitInputPrefix n inputCode))
          (preserveRightFuel (bitSliceFuel n))
          (initialNPOracleState outerInputLength
            (Nat.pair (bitSliceInput 0 n inputCode)
              (occurrenceContextFour complement systematicBits index n
                (encodeBooleanCircuit circuit)))) =
        some
          (Nat.pair (bitInputPrefix n inputCode)
            (occurrenceContextFour complement systematicBits index n
              (encodeBooleanCircuit circuit))) :=
    run_preserveRightProgram bitSliceProgram outerInputLength
      (bitSliceBits outerInputLength 0 n inputCode) (bitSliceFuel n)
      (bitSliceInput 0 n inputCode)
      (occurrenceContextFour complement systematicBits index n
        (encodeBooleanCircuit circuit))
      (bitInputPrefix n inputCode) hwindow
  have hhonest :
      runNPOracleProgram (preserveRightProgram (honestCallProgram factory))
          (preserveRightBits
            (honestCallBits factory outerInputLength circuit inputCode)
            (nativeInputRequest n (honestRequestCode circuit inputCode))
            (occurrenceContextFive complement systematicBits index)
            (occurrenceHonestCode factory circuit
              (bitInputPrefixView n inputCode)))
          (preserveRightFuel (honestCallFuel factory circuit inputCode))
          (initialNPOracleState outerInputLength
            (Nat.pair
              (nativeInputRequest n (honestRequestCode circuit inputCode))
              (occurrenceContextFive complement systematicBits index))) =
        some
          (Nat.pair
            (occurrenceHonestCode factory circuit
              (bitInputPrefixView n inputCode))
            (occurrenceContextFive complement systematicBits index)) :=
    run_preserveRightProgram (honestCallProgram factory) outerInputLength
      (honestCallBits factory outerInputLength circuit inputCode)
      (honestCallFuel factory circuit inputCode)
      (nativeInputRequest n (honestRequestCode circuit inputCode))
      (occurrenceContextFive complement systematicBits index)
      (occurrenceHonestCode factory circuit (bitInputPrefixView n inputCode))
      (run_honestCallProgram factory outerInputLength circuit inputCode)
  exact run_occurrenceStage
    (run_honestSlicePrepProgram outerInputLength index complement
      systematicBits n (encodeBooleanCircuit circuit) inputCode)
    (run_occurrenceStage hslice
      (run_occurrenceStage
        (run_honestPrepProgram outerInputLength (bitInputPrefix n inputCode)
          complement systematicBits index n (encodeBooleanCircuit circuit))
        (run_occurrenceStage hhonest
          (run_auxiliaryFinishProgram outerInputLength
            (occurrenceHonestCode factory circuit
              (bitInputPrefixView n inputCode))
            complement systematicBits index))))

/-! ## 7. Derived coordinates of one occurrence request -/

/-- The clause address of a requested occurrence: the interior digit window of
its public code. -/
def occurrenceAddressCode (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  bitSlice n (factory.forCircuit circuit).clauseBits inputCode

/-- The occurrence position digit of a requested occurrence. -/
def occurrencePositionDigit (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  (inputCode.testBit (n + (factory.forCircuit circuit).clauseBits)).toNat

/-- The literal code selected by a requested occurrence. -/
def occurrenceLiteralWord (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  occurrenceLiteralField
    (occurrenceClauseCode factory circuit
      (occurrenceAddressCode factory circuit inputCode))
    (occurrencePositionDigit factory circuit inputCode)

/-- The complement digit of the selected literal. -/
def occurrenceComplementDigit (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  ((Nat.unpair (occurrenceLiteralWord factory circuit inputCode)).1.testBit
    0).toNat

/-- The assignment coordinate named by the selected literal. -/
def occurrenceIndexValue (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  (Nat.unpair (occurrenceLiteralWord factory circuit inputCode)).2 %
    ((factory.forCircuit circuit).systematicBits +
      (factory.forCircuit circuit).auxiliaryBits)

/-- The context word carried across the clause and literal calls. -/
def occurrenceCallContext (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  occurrenceContextOne (occurrencePositionDigit factory circuit inputCode)
    (factory.forCircuit circuit).systematicBits
    ((factory.forCircuit circuit).systematicBits +
      (factory.forCircuit circuit).auxiliaryBits)
    n (encodeBooleanCircuit circuit) inputCode

/-- The payload handed to whichever assignment branch is selected. -/
def occurrenceBranchPayload (factory : ExecutablePointwisePCPPFactory)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  Nat.pair (occurrenceIndexValue factory circuit inputCode)
    (occurrenceContextTwo (occurrenceComplementDigit factory circuit inputCode)
      (factory.forCircuit circuit).systematicBits n
      (encodeBooleanCircuit circuit) inputCode)

private theorem occurrenceLiteralCode_eq_word
    (factory : ExecutablePointwisePCPPFactory) {n : ℕ}
    (circuit : BooleanCircuit n) (inputCode : ℕ) :
    occurrenceLiteralCode factory circuit
        (occurrenceAddressCode factory circuit inputCode)
        (inputCode.testBit (n + (factory.forCircuit circuit).clauseBits)) =
      occurrenceLiteralWord factory circuit inputCode := by
  unfold occurrenceLiteralWord occurrenceLiteralField occurrenceLiteralCode
    occurrencePositionDigit
  cases inputCode.testBit (n + (factory.forCircuit circuit).clauseBits) <;>
    simp

/-- The requested occurrence value, split into the assignment digit selected by
the literal and the literal's own complement digit. -/
private theorem occurrenceCodeValue_toNat_eq
    (factory : ExecutablePointwisePCPPFactory) {n : ℕ}
    (circuit : BooleanCircuit n) (inputCode : ℕ) :
    (((occurrenceAssignmentBit factory circuit (bitInputPrefixView n inputCode)
          (occurrenceIndexValue factory circuit inputCode)).toNat +
        occurrenceComplementDigit factory circuit inputCode).testBit 0).toNat =
      (occurrenceCodeValue factory circuit inputCode).toNat := by
  unfold occurrenceCodeValue occurrenceValue
  rw [show
    bitSlice n (factory.forCircuit circuit).clauseBits inputCode =
      occurrenceAddressCode factory circuit inputCode from rfl]
  rw [occurrenceLiteralCode_eq_word factory circuit inputCode]
  unfold occurrenceComplementDigit occurrenceIndexValue
  exact testBit_zero_toNat_add _ _

/-! ## 8. The assembled occurrence program -/

/-- The single fixed program computing one honest Case-2 occurrence bit of the
published factory from the public occurrence request. -/
def caseTwoOccurrenceProgram (factory : ExecutablePointwisePCPPFactory) :
    NPOracleProgram :=
  linkPrograms shapePrepProgram <|
    linkPrograms (preserveRightProgram (shapeCallProgram factory)) <|
      linkPrograms widthPrepProgram <|
        linkPrograms (preserveRightProgram bitSliceProgram) <|
          linkPrograms clausePrepProgram <|
            linkPrograms (preserveRightProgram (clauseCallProgram factory)) <|
              linkPrograms literalPrepProgram <|
                linkPrograms (preserveRightProgram literalDecodeProgram) <|
                  linkPrograms branchPrepProgram <|
                    linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram

theorem caseTwoOccurrenceProgram_oracleFree
    (factory : ExecutablePointwisePCPPFactory) :
    OracleFree (caseTwoOccurrenceProgram factory) := by
  apply oracleFree_linkPrograms shapePrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree (shapeCallProgram factory)
      (shapeCallProgram_oracleFree factory)
  apply oracleFree_linkPrograms widthPrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree bitSliceProgram
      bitSliceProgram_oracleFree
  apply oracleFree_linkPrograms clausePrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree (clauseCallProgram factory)
      (clauseCallProgram_oracleFree factory)
  apply oracleFree_linkPrograms literalPrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree literalDecodeProgram
      literalDecodeProgram_oracleFree
  apply oracleFree_linkPrograms branchPrepProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact taggedProgramChoice_oracleFree _ _
      (caseTwoAuxiliaryBranchProgram_oracleFree factory)
      (caseTwoSystematicBranchProgram_oracleFree factory)
  · exact xorFinishProgram_oracleFree

/-- One fuel charge covering either assignment branch. -/
def occurrenceBranchFuel (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) : ℕ :=
  max (caseTwoAuxiliaryBranchFuel factory circuit inputCode)
    (caseTwoSystematicBranchFuel factory inputLength circuit
      (occurrenceIndexValue factory circuit inputCode) inputCode)

/-- One register width covering either assignment branch. -/
def occurrenceBranchBits (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) : ℕ :=
  max
    (caseTwoAuxiliaryBranchBits factory inputLength circuit
      (occurrenceIndexValue factory circuit inputCode)
      (occurrenceComplementDigit factory circuit inputCode)
      (factory.forCircuit circuit).systematicBits inputCode)
    (caseTwoSystematicBranchBits factory inputLength circuit
      (occurrenceIndexValue factory circuit inputCode)
      (occurrenceComplementDigit factory circuit inputCode)
      (factory.forCircuit circuit).systematicBits inputCode)

/-- Register width of the assignment dispatcher itself. -/
def occurrenceChoiceBits (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) : ℕ :=
  max
    (natBitLength
      (Nat.pair inputLength
        (Nat.pair
          ((factory.forCircuit circuit).systematicBits -
            occurrenceIndexValue factory circuit inputCode)
          (occurrenceBranchPayload factory circuit inputCode)))) <|
    max (occurrenceBranchBits factory inputLength circuit inputCode) <|
      max
        (natBitLength
          (Nat.pair
            ((supportMaskBits
              (occurrenceSupportCode factory circuit
                (occurrenceIndexValue factory circuit inputCode))
              (bitInputPrefixView n inputCode)).foldl xor false).toNat
            (occurrenceComplementDigit factory circuit inputCode)))
        (natBitLength
          (Nat.pair
            ((occurrenceHonestCode factory circuit
              (bitInputPrefixView n inputCode)).testBit
                (occurrenceIndexValue factory circuit inputCode -
                  (factory.forCircuit circuit).systematicBits)).toNat
            (occurrenceComplementDigit factory circuit inputCode)))

/-- Total fuel of the assembled occurrence program. -/
def caseTwoOccurrenceFuel (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram (shapeCallProgram factory))
      (linkPrograms widthPrepProgram
        (linkPrograms (preserveRightProgram bitSliceProgram)
          (linkPrograms clausePrepProgram
            (linkPrograms (preserveRightProgram (clauseCallProgram factory))
              (linkPrograms literalPrepProgram
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram)))))))))
    shapePrepFuel <|
    linkFuel
      (linkPrograms widthPrepProgram
        (linkPrograms (preserveRightProgram bitSliceProgram)
          (linkPrograms clausePrepProgram
            (linkPrograms (preserveRightProgram (clauseCallProgram factory))
              (linkPrograms literalPrepProgram
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram))))))))
      (preserveRightFuel (shapeCallFuel factory circuit)) <|
      linkFuel
        (linkPrograms (preserveRightProgram bitSliceProgram)
          (linkPrograms clausePrepProgram
            (linkPrograms (preserveRightProgram (clauseCallProgram factory))
              (linkPrograms literalPrepProgram
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram)))))))
        widthPrepFuel <|
        linkFuel
          (linkPrograms clausePrepProgram
            (linkPrograms (preserveRightProgram (clauseCallProgram factory))
              (linkPrograms literalPrepProgram
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram))))))
          (preserveRightFuel
            (bitSliceFuel (factory.forCircuit circuit).clauseBits)) <|
          linkFuel
            (linkPrograms (preserveRightProgram (clauseCallProgram factory))
              (linkPrograms literalPrepProgram
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram)))))
            clausePrepFuel <|
            linkFuel
              (linkPrograms literalPrepProgram
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram))))
              (preserveRightFuel
                (clauseCallFuel factory circuit
                  (occurrenceAddressCode factory circuit inputCode))) <|
              linkFuel
                (linkPrograms (preserveRightProgram literalDecodeProgram)
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram)))
                literalPrepFuel <|
                linkFuel
                  (linkPrograms branchPrepProgram
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram))
                  (preserveRightFuel
                    (literalDecodeFuel
                      ((factory.forCircuit circuit).systematicBits +
                        (factory.forCircuit circuit).auxiliaryBits)
                      (occurrenceLiteralWord factory circuit inputCode))) <|
                  linkFuel
                    (linkPrograms
                      (taggedProgramChoice
                        (caseTwoAuxiliaryBranchProgram factory)
                        (caseTwoSystematicBranchProgram factory))
                      xorFinishProgram)
                    branchPrepFuel <|
                    linkFuel xorFinishProgram
                      (taggedProgramChoiceFuel
                        (occurrenceBranchFuel factory inputLength circuit
                          inputCode))
                      xorFinishFuel

/-- Total register width of the assembled occurrence program. -/
noncomputable def caseTwoOccurrenceBits
    (factory : ExecutablePointwisePCPPFactory) (inputLength : ℕ)
    {n : ℕ} (circuit : BooleanCircuit n) (inputCode : ℕ) : ℕ :=
  occurrenceStageBits inputLength
    (shapePrepBits n circuit.size (encodeBooleanCircuit circuit) inputCode) <|
    occurrenceStageBits inputLength
      (preserveRightBits (shapeCallBits factory inputLength circuit)
        (nativeInputRequest n (encodeBooleanCircuit circuit))
        (occurrenceContextZero n (encodeBooleanCircuit circuit) inputCode)
        (occurrenceShapeCode factory circuit)) <|
      occurrenceStageBits inputLength
        (widthPrepBits (occurrenceShapeCode factory circuit) n
          (encodeBooleanCircuit circuit) inputCode) <|
        occurrenceStageBits inputLength
          (preserveRightBits
            (bitSliceBits inputLength n
              (factory.forCircuit circuit).clauseBits inputCode)
            (bitSliceInput n (factory.forCircuit circuit).clauseBits inputCode)
            (occurrenceCallContext factory circuit inputCode)
            (occurrenceAddressCode factory circuit inputCode)) <|
          occurrenceStageBits inputLength
            (clausePrepBits (occurrenceAddressCode factory circuit inputCode)
              (occurrencePositionDigit factory circuit inputCode)
              (factory.forCircuit circuit).systematicBits
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              n (encodeBooleanCircuit circuit) inputCode) <|
            occurrenceStageBits inputLength
              (preserveRightBits
                (clauseCallBits factory inputLength circuit
                  (occurrenceAddressCode factory circuit inputCode))
                (nativeInputRequest n
                  (clauseRequestCode circuit
                    (occurrenceAddressCode factory circuit inputCode)))
                (occurrenceCallContext factory circuit inputCode)
                (occurrenceClauseCode factory circuit
                  (occurrenceAddressCode factory circuit inputCode))) <|
              occurrenceStageBits inputLength
                (literalPrepBits
                  (occurrenceClauseCode factory circuit
                    (occurrenceAddressCode factory circuit inputCode))
                  (occurrencePositionDigit factory circuit inputCode)
                  (factory.forCircuit circuit).systematicBits
                  ((factory.forCircuit circuit).systematicBits +
                    (factory.forCircuit circuit).auxiliaryBits)
                  n (encodeBooleanCircuit circuit) inputCode) <|
                occurrenceStageBits inputLength
                  (preserveRightBits
                    (literalDecodeBits inputLength
                      ((factory.forCircuit circuit).systematicBits +
                        (factory.forCircuit circuit).auxiliaryBits)
                      (occurrenceLiteralWord factory circuit inputCode))
                    (literalDecodeInput
                      ((factory.forCircuit circuit).systematicBits +
                        (factory.forCircuit circuit).auxiliaryBits)
                      (occurrenceLiteralWord factory circuit inputCode))
                    (occurrenceCallContext factory circuit inputCode)
                    (literalDecodeOutput
                      ((factory.forCircuit circuit).systematicBits +
                        (factory.forCircuit circuit).auxiliaryBits)
                      (occurrenceLiteralWord factory circuit inputCode))) <|
                  occurrenceStageBits inputLength
                    (branchPrepBits
                      (occurrenceComplementDigit factory circuit inputCode)
                      (occurrenceIndexValue factory circuit inputCode)
                      (occurrencePositionDigit factory circuit inputCode)
                      (factory.forCircuit circuit).systematicBits
                      ((factory.forCircuit circuit).systematicBits +
                        (factory.forCircuit circuit).auxiliaryBits)
                      n (encodeBooleanCircuit circuit) inputCode) <|
                    occurrenceStageBits inputLength
                      (occurrenceChoiceBits factory inputLength circuit
                        inputCode)
                      (xorFinishBits
                        (occurrenceAssignmentBit factory circuit
                          (bitInputPrefixView n inputCode)
                          (occurrenceIndexValue factory circuit
                            inputCode)).toNat
                        (occurrenceComplementDigit factory circuit inputCode))

/-- **Exact execution of the assembled Case-2 occurrence program.**  From the
public occurrence request alone the fixed program returns the honest
occurrence bit of the published factory: one `shapeRunner` call, one
`clauseRunner` call, one literal decode, one `supportRunner` or `honestRunner`
call selected by the decoded coordinate, and one complementing digit. -/
theorem run_caseTwoOccurrenceProgram
    (factory : ExecutablePointwisePCPPFactory)
    (inputLength : ℕ) {n : ℕ} (circuit : BooleanCircuit n)
    (inputCode : ℕ) :
    runNPOracleProgram (caseTwoOccurrenceProgram factory)
        (caseTwoOccurrenceBits factory inputLength circuit inputCode)
        (caseTwoOccurrenceFuel factory inputLength circuit inputCode)
        (initialNPOracleState inputLength
          (caseTwoOccurrenceInput n circuit.size
            (encodeBooleanCircuit circuit) inputCode)) =
      some (occurrenceCodeValue factory circuit inputCode).toNat := by
  have hshapePrep :
      runNPOracleProgram shapePrepProgram
          (shapePrepBits n circuit.size (encodeBooleanCircuit circuit)
            inputCode)
          shapePrepFuel
          (initialNPOracleState inputLength
            (caseTwoOccurrenceInput n circuit.size
              (encodeBooleanCircuit circuit) inputCode)) =
        some
          (Nat.pair (nativeInputRequest n (encodeBooleanCircuit circuit))
            (occurrenceContextZero n (encodeBooleanCircuit circuit)
              inputCode)) :=
    run_shapePrepProgram inputLength n circuit.size
      (encodeBooleanCircuit circuit) inputCode
  have hshapeCall :
      runNPOracleProgram (preserveRightProgram (shapeCallProgram factory))
          (preserveRightBits (shapeCallBits factory inputLength circuit)
            (nativeInputRequest n (encodeBooleanCircuit circuit))
            (occurrenceContextZero n (encodeBooleanCircuit circuit) inputCode)
            (occurrenceShapeCode factory circuit))
          (preserveRightFuel (shapeCallFuel factory circuit))
          (initialNPOracleState inputLength
            (Nat.pair (nativeInputRequest n (encodeBooleanCircuit circuit))
              (occurrenceContextZero n (encodeBooleanCircuit circuit)
                inputCode))) =
        some
          (Nat.pair (occurrenceShapeCode factory circuit)
            (occurrenceContextZero n (encodeBooleanCircuit circuit)
              inputCode)) :=
    run_preserveRightProgram (shapeCallProgram factory) inputLength
      (shapeCallBits factory inputLength circuit)
      (shapeCallFuel factory circuit)
      (nativeInputRequest n (encodeBooleanCircuit circuit))
      (occurrenceContextZero n (encodeBooleanCircuit circuit) inputCode)
      (occurrenceShapeCode factory circuit)
      (run_shapeCallProgram factory inputLength circuit)
  have hwidth :
      runNPOracleProgram widthPrepProgram
          (widthPrepBits (occurrenceShapeCode factory circuit) n
            (encodeBooleanCircuit circuit) inputCode)
          widthPrepFuel
          (initialNPOracleState inputLength
            (Nat.pair (occurrenceShapeCode factory circuit)
              (occurrenceContextZero n (encodeBooleanCircuit circuit)
                inputCode))) =
        some
          (Nat.pair
            (bitSliceInput n (factory.forCircuit circuit).clauseBits inputCode)
            (occurrenceCallContext factory circuit inputCode)) :=
    run_widthPrepProgram inputLength (occurrenceShapeCode factory circuit) n
      (encodeBooleanCircuit circuit) inputCode
  have haddress :
      runNPOracleProgram (preserveRightProgram bitSliceProgram)
          (preserveRightBits
            (bitSliceBits inputLength n
              (factory.forCircuit circuit).clauseBits inputCode)
            (bitSliceInput n (factory.forCircuit circuit).clauseBits inputCode)
            (occurrenceCallContext factory circuit inputCode)
            (occurrenceAddressCode factory circuit inputCode))
          (preserveRightFuel
            (bitSliceFuel (factory.forCircuit circuit).clauseBits))
          (initialNPOracleState inputLength
            (Nat.pair
              (bitSliceInput n (factory.forCircuit circuit).clauseBits
                inputCode)
              (occurrenceCallContext factory circuit inputCode))) =
        some
          (Nat.pair (occurrenceAddressCode factory circuit inputCode)
            (occurrenceCallContext factory circuit inputCode)) :=
    run_preserveRightProgram bitSliceProgram inputLength
      (bitSliceBits inputLength n (factory.forCircuit circuit).clauseBits
        inputCode)
      (bitSliceFuel (factory.forCircuit circuit).clauseBits)
      (bitSliceInput n (factory.forCircuit circuit).clauseBits inputCode)
      (occurrenceCallContext factory circuit inputCode)
      (occurrenceAddressCode factory circuit inputCode)
      (run_bitSliceProgram inputLength n
        (factory.forCircuit circuit).clauseBits inputCode)
  have hclausePrep :
      runNPOracleProgram clausePrepProgram
          (clausePrepBits (occurrenceAddressCode factory circuit inputCode)
            (occurrencePositionDigit factory circuit inputCode)
            (factory.forCircuit circuit).systematicBits
            ((factory.forCircuit circuit).systematicBits +
              (factory.forCircuit circuit).auxiliaryBits)
            n (encodeBooleanCircuit circuit) inputCode)
          clausePrepFuel
          (initialNPOracleState inputLength
            (Nat.pair (occurrenceAddressCode factory circuit inputCode)
              (occurrenceCallContext factory circuit inputCode))) =
        some
          (Nat.pair
            (nativeInputRequest n
              (clauseRequestCode circuit
                (occurrenceAddressCode factory circuit inputCode)))
            (occurrenceCallContext factory circuit inputCode)) :=
    run_clausePrepProgram inputLength
      (occurrenceAddressCode factory circuit inputCode)
      (occurrencePositionDigit factory circuit inputCode)
      (factory.forCircuit circuit).systematicBits
      ((factory.forCircuit circuit).systematicBits +
        (factory.forCircuit circuit).auxiliaryBits)
      n (encodeBooleanCircuit circuit) inputCode
  have hclauseCall :
      runNPOracleProgram (preserveRightProgram (clauseCallProgram factory))
          (preserveRightBits
            (clauseCallBits factory inputLength circuit
              (occurrenceAddressCode factory circuit inputCode))
            (nativeInputRequest n
              (clauseRequestCode circuit
                (occurrenceAddressCode factory circuit inputCode)))
            (occurrenceCallContext factory circuit inputCode)
            (occurrenceClauseCode factory circuit
              (occurrenceAddressCode factory circuit inputCode)))
          (preserveRightFuel
            (clauseCallFuel factory circuit
              (occurrenceAddressCode factory circuit inputCode)))
          (initialNPOracleState inputLength
            (Nat.pair
              (nativeInputRequest n
                (clauseRequestCode circuit
                  (occurrenceAddressCode factory circuit inputCode)))
              (occurrenceCallContext factory circuit inputCode))) =
        some
          (Nat.pair
            (occurrenceClauseCode factory circuit
              (occurrenceAddressCode factory circuit inputCode))
            (occurrenceCallContext factory circuit inputCode)) :=
    run_preserveRightProgram (clauseCallProgram factory) inputLength
      (clauseCallBits factory inputLength circuit
        (occurrenceAddressCode factory circuit inputCode))
      (clauseCallFuel factory circuit
        (occurrenceAddressCode factory circuit inputCode))
      (nativeInputRequest n
        (clauseRequestCode circuit
          (occurrenceAddressCode factory circuit inputCode)))
      (occurrenceCallContext factory circuit inputCode)
      (occurrenceClauseCode factory circuit
        (occurrenceAddressCode factory circuit inputCode))
      (run_clauseCallProgram factory inputLength circuit
        (occurrenceAddressCode factory circuit inputCode))
  have hliteralPrep :
      runNPOracleProgram literalPrepProgram
          (literalPrepBits
            (occurrenceClauseCode factory circuit
              (occurrenceAddressCode factory circuit inputCode))
            (occurrencePositionDigit factory circuit inputCode)
            (factory.forCircuit circuit).systematicBits
            ((factory.forCircuit circuit).systematicBits +
              (factory.forCircuit circuit).auxiliaryBits)
            n (encodeBooleanCircuit circuit) inputCode)
          literalPrepFuel
          (initialNPOracleState inputLength
            (Nat.pair
              (occurrenceClauseCode factory circuit
                (occurrenceAddressCode factory circuit inputCode))
              (occurrenceCallContext factory circuit inputCode))) =
        some
          (Nat.pair
            (literalDecodeInput
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              (occurrenceLiteralWord factory circuit inputCode))
            (occurrenceCallContext factory circuit inputCode)) :=
    run_literalPrepProgram inputLength
      (occurrenceClauseCode factory circuit
        (occurrenceAddressCode factory circuit inputCode))
      (occurrencePositionDigit factory circuit inputCode)
      (factory.forCircuit circuit).systematicBits
      ((factory.forCircuit circuit).systematicBits +
        (factory.forCircuit circuit).auxiliaryBits)
      n (encodeBooleanCircuit circuit) inputCode
  have hliteralDecode :
      runNPOracleProgram (preserveRightProgram literalDecodeProgram)
          (preserveRightBits
            (literalDecodeBits inputLength
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              (occurrenceLiteralWord factory circuit inputCode))
            (literalDecodeInput
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              (occurrenceLiteralWord factory circuit inputCode))
            (occurrenceCallContext factory circuit inputCode)
            (literalDecodeOutput
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              (occurrenceLiteralWord factory circuit inputCode)))
          (preserveRightFuel
            (literalDecodeFuel
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              (occurrenceLiteralWord factory circuit inputCode)))
          (initialNPOracleState inputLength
            (Nat.pair
              (literalDecodeInput
                ((factory.forCircuit circuit).systematicBits +
                  (factory.forCircuit circuit).auxiliaryBits)
                (occurrenceLiteralWord factory circuit inputCode))
              (occurrenceCallContext factory circuit inputCode))) =
        some
          (Nat.pair
            (literalDecodeOutput
              ((factory.forCircuit circuit).systematicBits +
                (factory.forCircuit circuit).auxiliaryBits)
              (occurrenceLiteralWord factory circuit inputCode))
            (occurrenceCallContext factory circuit inputCode)) :=
    run_preserveRightProgram literalDecodeProgram inputLength
      (literalDecodeBits inputLength
        ((factory.forCircuit circuit).systematicBits +
          (factory.forCircuit circuit).auxiliaryBits)
        (occurrenceLiteralWord factory circuit inputCode))
      (literalDecodeFuel
        ((factory.forCircuit circuit).systematicBits +
          (factory.forCircuit circuit).auxiliaryBits)
        (occurrenceLiteralWord factory circuit inputCode))
      (literalDecodeInput
        ((factory.forCircuit circuit).systematicBits +
          (factory.forCircuit circuit).auxiliaryBits)
        (occurrenceLiteralWord factory circuit inputCode))
      (occurrenceCallContext factory circuit inputCode)
      (literalDecodeOutput
        ((factory.forCircuit circuit).systematicBits +
          (factory.forCircuit circuit).auxiliaryBits)
        (occurrenceLiteralWord factory circuit inputCode))
      (run_literalDecodeProgram inputLength
        ((factory.forCircuit circuit).systematicBits +
          (factory.forCircuit circuit).auxiliaryBits)
        (occurrenceLiteralWord factory circuit inputCode)
        (assignmentBits_positive factory circuit))
  have hbranchPrep :
      runNPOracleProgram branchPrepProgram
          (branchPrepBits (occurrenceComplementDigit factory circuit inputCode)
            (occurrenceIndexValue factory circuit inputCode)
            (occurrencePositionDigit factory circuit inputCode)
            (factory.forCircuit circuit).systematicBits
            ((factory.forCircuit circuit).systematicBits +
              (factory.forCircuit circuit).auxiliaryBits)
            n (encodeBooleanCircuit circuit) inputCode)
          branchPrepFuel
          (initialNPOracleState inputLength
            (Nat.pair
              (literalDecodeOutput
                ((factory.forCircuit circuit).systematicBits +
                  (factory.forCircuit circuit).auxiliaryBits)
                (occurrenceLiteralWord factory circuit inputCode))
              (occurrenceCallContext factory circuit inputCode))) =
        some
          (Nat.pair
            ((factory.forCircuit circuit).systematicBits -
              occurrenceIndexValue factory circuit inputCode)
            (occurrenceBranchPayload factory circuit inputCode)) :=
    run_branchPrepProgram inputLength
      (occurrenceComplementDigit factory circuit inputCode)
      (occurrenceIndexValue factory circuit inputCode)
      (occurrencePositionDigit factory circuit inputCode)
      (factory.forCircuit circuit).systematicBits
      ((factory.forCircuit circuit).systematicBits +
        (factory.forCircuit circuit).auxiliaryBits)
      n (encodeBooleanCircuit circuit) inputCode
  have hchoice :
      runNPOracleProgram
          (taggedProgramChoice (caseTwoAuxiliaryBranchProgram factory)
            (caseTwoSystematicBranchProgram factory))
          (occurrenceChoiceBits factory inputLength circuit inputCode)
          (taggedProgramChoiceFuel
            (occurrenceBranchFuel factory inputLength circuit inputCode))
          (initialNPOracleState inputLength
            (Nat.pair
              ((factory.forCircuit circuit).systematicBits -
                occurrenceIndexValue factory circuit inputCode)
              (occurrenceBranchPayload factory circuit inputCode))) =
        some
          (Nat.pair
            (occurrenceAssignmentBit factory circuit
              (bitInputPrefixView n inputCode)
              (occurrenceIndexValue factory circuit inputCode)).toNat
            (occurrenceComplementDigit factory circuit inputCode)) := by
    by_cases hindex :
        occurrenceIndexValue factory circuit inputCode <
          (factory.forCircuit circuit).systematicBits
    · rw [occurrenceAssignmentBit_systematic factory circuit
        (bitInputPrefixView n inputCode) hindex]
      have hwide :=
        run_bits_mono
          (newBits :=
            occurrenceChoiceBits factory inputLength circuit inputCode)
          (run_caseTwoSystematicBranchProgram factory inputLength circuit
            (occurrenceIndexValue factory circuit inputCode)
            (occurrenceComplementDigit factory circuit inputCode)
            (factory.forCircuit circuit).systematicBits inputCode)
          ((Nat.le_max_right _ _).trans
            ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
      have hbranchLe :
          caseTwoSystematicBranchFuel factory inputLength circuit
              (occurrenceIndexValue factory circuit inputCode) inputCode ≤
            occurrenceBranchFuel factory inputLength circuit inputCode :=
        Nat.le_max_right _ _
      have hfuel :=
        runNPOracleProgram_add_fuel_of_some
          (extra :=
            occurrenceBranchFuel factory inputLength circuit inputCode -
              caseTwoSystematicBranchFuel factory inputLength circuit
                (occurrenceIndexValue factory circuit inputCode) inputCode)
          hwide
      rw [Nat.add_sub_cancel' hbranchLe] at hfuel
      exact run_taggedProgramChoice_nonzero
        (caseTwoAuxiliaryBranchProgram factory)
        (caseTwoSystematicBranchProgram factory) inputLength
        ((factory.forCircuit circuit).systematicBits -
          occurrenceIndexValue factory circuit inputCode)
        (occurrenceBranchPayload factory circuit inputCode)
        (occurrenceChoiceBits factory inputLength circuit inputCode)
        (occurrenceBranchFuel factory inputLength circuit inputCode) _
        (by omega) (Nat.le_max_left _ _) hfuel
        ((Nat.le_max_left _ _).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
    · have hzero :
          (factory.forCircuit circuit).systematicBits -
            occurrenceIndexValue factory circuit inputCode = 0 := by
        omega
      have hpair :
          Nat.pair inputLength
              (Nat.pair 0
                (occurrenceBranchPayload factory circuit inputCode)) =
            Nat.pair inputLength
              (Nat.pair
                ((factory.forCircuit circuit).systematicBits -
                  occurrenceIndexValue factory circuit inputCode)
                (occurrenceBranchPayload factory circuit inputCode)) := by
        rw [hzero]
      have hinput :
          natBitLength
              (Nat.pair inputLength
                (Nat.pair 0
                  (occurrenceBranchPayload factory circuit inputCode))) ≤
            occurrenceChoiceBits factory inputLength circuit inputCode := by
        rw [hpair]
        exact Nat.le_max_left _ _
      rw [occurrenceAssignmentBit_auxiliary factory circuit
        (bitInputPrefixView n inputCode) hindex]
      rw [hzero]
      have hwide :=
        run_bits_mono
          (newBits :=
            occurrenceChoiceBits factory inputLength circuit inputCode)
          (run_caseTwoAuxiliaryBranchProgram factory inputLength circuit
            (occurrenceIndexValue factory circuit inputCode)
            (occurrenceComplementDigit factory circuit inputCode)
            (factory.forCircuit circuit).systematicBits inputCode)
          ((Nat.le_max_left _ _).trans
            ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
      have hbranchLe :
          caseTwoAuxiliaryBranchFuel factory circuit inputCode ≤
            occurrenceBranchFuel factory inputLength circuit inputCode :=
        Nat.le_max_left _ _
      have hfuel :=
        runNPOracleProgram_add_fuel_of_some
          (extra :=
            occurrenceBranchFuel factory inputLength circuit inputCode -
              caseTwoAuxiliaryBranchFuel factory circuit inputCode)
          hwide
      rw [Nat.add_sub_cancel' hbranchLe] at hfuel
      exact run_taggedProgramChoice_zero
        (caseTwoAuxiliaryBranchProgram factory)
        (caseTwoSystematicBranchProgram factory) inputLength
        (occurrenceBranchPayload factory circuit inputCode)
        (occurrenceChoiceBits factory inputLength circuit inputCode)
        (occurrenceBranchFuel factory inputLength circuit inputCode) _
        hinput hfuel
        ((Nat.le_max_right _ _).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hxor :
      runNPOracleProgram xorFinishProgram
          (xorFinishBits
            (occurrenceAssignmentBit factory circuit
              (bitInputPrefixView n inputCode)
              (occurrenceIndexValue factory circuit inputCode)).toNat
            (occurrenceComplementDigit factory circuit inputCode))
          xorFinishFuel
          (initialNPOracleState inputLength
            (Nat.pair
              (occurrenceAssignmentBit factory circuit
                (bitInputPrefixView n inputCode)
                (occurrenceIndexValue factory circuit inputCode)).toNat
              (occurrenceComplementDigit factory circuit inputCode))) =
        some
          (((occurrenceAssignmentBit factory circuit
            (bitInputPrefixView n inputCode)
            (occurrenceIndexValue factory circuit inputCode)).toNat +
              occurrenceComplementDigit factory circuit inputCode).testBit
                0).toNat :=
    run_xorFinishProgram inputLength
      (occurrenceAssignmentBit factory circuit (bitInputPrefixView n inputCode)
        (occurrenceIndexValue factory circuit inputCode)).toNat
      (occurrenceComplementDigit factory circuit inputCode)
  rw [← occurrenceCodeValue_toNat_eq factory circuit inputCode]
  exact run_occurrenceStage hshapePrep
    (run_occurrenceStage hshapeCall
      (run_occurrenceStage hwidth
        (run_occurrenceStage haddress
          (run_occurrenceStage hclausePrep
            (run_occurrenceStage hclauseCall
              (run_occurrenceStage hliteralPrep
                (run_occurrenceStage hliteralDecode
                  (run_occurrenceStage hbranchPrep
                    (run_occurrenceStage hchoice hxor)))))))))

end NearCubicWires.CaseTwoOccurrenceProgram
