import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalTaggedParityProgram
import Proof.CaseAnalysis.CaseTwoOccurrenceEvaluation
import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# The masked support parity of one Case-2 occurrence

`CaseTwoOccurrenceEvaluation.parityOn_decodeSupport_eq_maskFold` reduces the
systematic half of one occurrence assignment to the exclusive-or fold of the
masked digit list `supportMaskBits`.  This module executes that fold with the
production controller: canonical range generation, one balanced call per index
to a fixed two-digit mask program, and the shared balanced parity substrate of
`CanonicalTaggedParityProgram`.

No decoded support list, `Finset`, or host parity callback crosses the
executable boundary: the support word returned by the factory's
`supportRunner` is read one digit at a time, in place, by the same program for
every index.
-/

namespace NearCubicWires.CaseTwoOccurrenceParityProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed two-digit mask callee -/

/-- Range context shared by every masked digit: the support word returned by
one `supportRunner` call, beside the public occurrence input code. -/
def maskContext (supportCode inputCode : ℕ) : ℕ :=
  Nat.pair supportCode inputCode

/-- Callee ABI: `pair(index, maskContext)`, the tail of one canonical range
request atom. -/
def maskBitInput (index supportCode inputCode : ℕ) : ℕ :=
  Nat.pair index (maskContext supportCode inputCode)

/-- Proof-level value of the mask callee at one whole request atom. -/
def maskBitValue (request : ℕ) : Bool :=
  (Nat.unpair (Nat.unpair (Nat.unpair request).2).2).1.testBit
      (Nat.unpair (Nat.unpair request).2).1 &&
    (Nat.unpair (Nat.unpair (Nat.unpair request).2).2).2.testBit
      (Nat.unpair (Nat.unpair request).2).1

@[simp] theorem maskBitValue_atom
    (inputLength index supportCode inputCode : ℕ) :
    maskBitValue
        (balancedRangeRequestAtom inputLength index
          (maskContext supportCode inputCode)) =
      (supportCode.testBit index && inputCode.testBit index) := by
  simp [maskBitValue, balancedRangeRequestAtom, maskContext]

/-!
Register ABI of the mask callee:

* `r0`: request tail, then output;
* `r2`: digit index;
* `r3`: mask context;
* `r4`: support word;
* `r5`: occurrence input code;
* `r6`: support digit;
* `r7`: input digit.
-/
def maskBitProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .testBit 4 2 6 5
  , .testBit 5 2 7 6
  , .branchZero 6 8 7
  , .copy 7 0 9
  , .set 0 0 9
  , .halt 0
  ]

@[simp] theorem maskBitProgram_oracleFree :
    OracleFree maskBitProgram := by
  rfl

def maskBitFuel : ℕ := 9

theorem run_maskBitProgram
    (inputLength index supportCode inputCode maximumBits : ℕ)
    (hinput :
      natBitLength (maskBitInput index supportCode inputCode) ≤ maximumBits)
    (hone : 1 ≤ maximumBits) :
    runNPOracleProgram maskBitProgram maximumBits maskBitFuel
        (initialNPOracleState inputLength
          (maskBitInput index supportCode inputCode)) =
      some (boolCode (supportCode.testBit index && inputCode.testBit index)) := by
  let context := maskContext supportCode inputCode
  let supportDigit := (supportCode.testBit index).toNat
  let inputDigit := (inputCode.testBit index).toNat
  have hsmallBits : ∀ value : ℕ, value ≤ 1 → natBitLength value ≤ maximumBits := by
    intro value hvalue
    apply le_trans ?_ hone
    interval_cases value <;> simp [natBitLength]
  have hindexBits : natBitLength index ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hinput
    simpa only [maskBitInput] using Nat.left_le_pair index context
  have hcontextBits : natBitLength context ≤ maximumBits := by
    apply (natBitLength_mono ?_).trans hinput
    simpa only [maskBitInput] using Nat.right_le_pair index context
  have hsupportBits : natBitLength supportCode ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.left_le_pair supportCode inputCode)).trans
        hcontextBits
  have hinputCodeBits : natBitLength inputCode ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.right_le_pair supportCode inputCode)).trans
        hcontextBits
  have hsupportDigitBits : natBitLength supportDigit ≤ maximumBits := by
    apply hsmallBits
    unfold supportDigit
    cases supportCode.testBit index <;> simp
  have hinputDigitBits : natBitLength inputDigit ≤ maximumBits := by
    apply hsmallBits
    unfold inputDigit
    cases inputCode.testBit index <;> simp
  have hzeroBits : natBitLength 0 ≤ maximumBits := hsmallBits 0 (by omega)
  rw [show maskBitFuel = 8 + 1 by rfl]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState, maskBitInput])
    hindexBits]
  rw [show 8 = 7 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump,
        maskBitInput, context])
    hcontextBits]
  rw [show 7 = 6 + 1 by omega]
  rw [run_unpairLeft_instruction (value := supportCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, maskContext])
    hsupportBits]
  rw [show 6 = 5 + 1 by omega]
  rw [run_unpairRight_instruction (value := inputCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, context, maskContext])
    hinputCodeBits]
  rw [show 5 = 4 + 1 by omega]
  rw [run_testBit_instruction (value := supportDigit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, supportDigit])
    hsupportDigitBits]
  rw [show 4 = 3 + 1 by omega]
  rw [run_testBit_instruction (value := inputDigit)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, inputDigit])
    hinputDigitBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction (by rfl) rfl]
  by_cases hsupportDigit : supportCode.testBit index = true
  · rw [show
      (if
          ((((((initialNPOracleState inputLength
            (maskBitInput index supportCode inputCode)).write 2
              index).jump 1).write 3 context).jump 2).write 4
                supportCode |>.jump 3 |>.write 5 inputCode |>.jump 4 |>.write 6
                  supportDigit |>.jump 5 |>.write 7 inputDigit |>.jump
                    6).registers 6 = 0 then 8 else 7) = 7 by
      simp [NPOracleState.write, NPOracleState.jump, supportDigit,
        hsupportDigit]]
    rw [show 2 = 1 + 1 by omega]
    rw [run_copy_instruction (value := inputDigit)
      (by rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hinputDigitBits]
    exact run_halt_instruction (fuel := 0) (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, inputDigit, boolCode,
          hsupportDigit])
      (by
        simpa only [boolCode, hsupportDigit, Bool.true_and] using
          hinputDigitBits)
  · simp only [Bool.not_eq_true] at hsupportDigit
    rw [show
      (if
          ((((((initialNPOracleState inputLength
            (maskBitInput index supportCode inputCode)).write 2
              index).jump 1).write 3 context).jump 2).write 4
                supportCode |>.jump 3 |>.write 5 inputCode |>.jump 4 |>.write 6
                  supportDigit |>.jump 5 |>.write 7 inputDigit |>.jump
                    6).registers 6 = 0 then 8 else 7) = 8 by
      simp [NPOracleState.write, NPOracleState.jump, supportDigit,
        hsupportDigit]]
    rw [show 2 = 1 + 1 by omega]
    rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
    exact run_halt_instruction (fuel := 0) (by rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, boolCode,
          hsupportDigit])
      (by
        simpa only [boolCode, hsupportDigit, Bool.false_and,
          Bool.toNat_false] using hzeroBits)

/-! ## 2. Dropping the retained range context -/

def dropRightProgram : NPOracleProgram :=
  [ .unpairLeft 0 0 1
  , .halt 0
  ]

@[simp] theorem dropRightProgram_oracleFree :
    OracleFree dropRightProgram := by
  rfl

def dropRightBits (left right : ℕ) : ℕ :=
  max (natBitLength (Nat.pair left right)) (natBitLength left)

theorem run_dropRightProgram (inputLength left right : ℕ) :
    runNPOracleProgram dropRightProgram (dropRightBits left right) 2
        (initialNPOracleState inputLength (Nat.pair left right)) =
      some left := by
  have hleft : natBitLength left ≤ dropRightBits left right :=
    Nat.le_max_right _ _
  rw [show 2 = 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := left)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hleft]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hleft

/-! ## 3. The complete masked parity stage -/

def maskedParityRequests
    (inputLength arity supportCode inputCode : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength
    (maskContext supportCode inputCode) 0 arity

def maskedParityValues
    (inputLength arity supportCode inputCode : ℕ) : List Bool :=
  (maskedParityRequests inputLength arity supportCode inputCode).map
    maskBitValue

private theorem le_foldr_max_of_mem
    {value : ℕ} {values : List ℕ} (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head tail inductionHypothesis =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hmem).trans (Nat.le_max_right _ _)

/-- One width covering the mask callee at every generated index. -/
def maskedParityCalleeBits
    (inputLength arity supportCode inputCode : ℕ) : ℕ :=
  max 1
    (((maskedParityRequests inputLength arity supportCode inputCode).map
      fun request => natBitLength (Nat.unpair request).2).foldr max 0)

def maskedParityCallBits
    (inputLength arity supportCode inputCode : ℕ) : ℕ :=
  max (maskedParityCalleeBits inputLength arity supportCode inputCode)
    (balancedCallRequiredBits (fun request => boolCode (maskBitValue request))
      (maskedParityRequests inputLength arity supportCode inputCode))

def maskedParityBits
    (inputLength arity supportCode inputCode : ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (generatedBalancedRangeRequiredBits inputLength arity
        (maskContext supportCode inputCode)) <|
      max
        (preserveRightBits
          (maskedParityCallBits inputLength arity supportCode inputCode)
          (encodeBalancedList
            (maskedParityRequests inputLength arity supportCode inputCode))
          (maskContext supportCode inputCode)
          (encodeBoolList
            (maskedParityValues inputLength arity supportCode inputCode))) <|
        max
          (dropRightBits
            (encodeBoolList
              (maskedParityValues inputLength arity supportCode inputCode))
            (maskContext supportCode inputCode))
          (balancedBitParityBits inputLength
            ((maskedParityValues inputLength arity supportCode
              inputCode).map boolCode))

def maskedParityTailFuel
    (inputLength arity supportCode inputCode : ℕ) : ℕ :=
  linkFuel balancedBitParityProgram 2
    (balancedBitParityFuel
      ((maskedParityValues inputLength arity supportCode inputCode).map
        boolCode))

def maskedParityAfterRangeFuel
    (inputLength arity supportCode inputCode : ℕ) : ℕ :=
  linkFuel (linkPrograms dropRightProgram balancedBitParityProgram)
    (preserveRightFuel
      (balancedCallFuel maskBitProgram (fun _ => maskBitFuel)
        (maskedParityRequests inputLength arity supportCode inputCode)))
    (maskedParityTailFuel inputLength arity supportCode inputCode)

def maskedParityFuel
    (inputLength arity supportCode inputCode : ℕ) : ℕ :=
  linkFuel
    (linkPrograms (preserveRightProgram (balancedCallProgram maskBitProgram))
      (linkPrograms dropRightProgram balancedBitParityProgram))
    (generatedBalancedRangeFuel inputLength arity
      (maskContext supportCode inputCode))
    (maskedParityAfterRangeFuel inputLength arity supportCode inputCode)

/-- The single production controller for one masked support parity. -/
def maskedParityProgram : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram <|
    linkPrograms (preserveRightProgram (balancedCallProgram maskBitProgram)) <|
      linkPrograms dropRightProgram balancedBitParityProgram

theorem maskedParityProgram_oracleFree :
    OracleFree maskedParityProgram := by
  apply oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree (balancedCallProgram maskBitProgram)
      (balancedCallProgram_oracleFree maskBitProgram_oracleFree)
  · exact oracleFree_linkPrograms dropRightProgram_oracleFree
      balancedBitParityProgram_oracleFree

private theorem maskedParityValues_eq_supportMaskBits
    (inputLength arity supportCode inputCode : ℕ) :
    maskedParityValues inputLength arity supportCode inputCode =
      supportMaskBits supportCode (bitInputPrefixView arity inputCode) := by
  unfold maskedParityValues maskedParityRequests
  rw [balancedRangeRequestAtoms_eq_map_range, List.map_map, supportMaskBits]
  apply List.map_congr_left
  intro offset hoffset
  have hbound : offset < arity := List.mem_range.mp hoffset
  rw [Function.comp_apply, Nat.zero_add, maskBitValue_atom,
    supportMaskBit_prefixView]
  simp [hbound]

/-- **Exact execution of the masked support parity.**  The output is the
`Bool.toNat` code of the exclusive-or fold that
`parityOn_decodeSupport_eq_maskFold` identifies with the semantic parity of
the decoded support. -/
theorem run_maskedParityProgram
    (inputLength arity supportCode inputCode : ℕ) :
    runNPOracleProgram maskedParityProgram
        (maskedParityBits inputLength arity supportCode inputCode)
        (maskedParityFuel inputLength arity supportCode inputCode)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput arity
            (maskContext supportCode inputCode))) =
      some
        ((supportMaskBits supportCode
          (bitInputPrefixView arity inputCode)).foldl xor false).toNat := by
  let context := maskContext supportCode inputCode
  let requests := maskedParityRequests inputLength arity supportCode inputCode
  let values := maskedParityValues inputLength arity supportCode inputCode
  let requestTree := encodeBalancedList requests
  let valueTree := encodeBoolList values
  let callBits := maskedParityCallBits inputLength arity supportCode inputCode
  let maximumBits := maskedParityBits inputLength arity supportCode inputCode
  have hlengthBits : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hlengthBits
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength arity context ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpreserveBits :
      preserveRightBits callBits requestTree context valueTree ≤
        maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hdropBits :
      dropRightBits valueTree context ≤ maximumBits := by
    exact
      (Nat.le_max_left _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hparityBits :
      balancedBitParityBits inputLength (values.map boolCode) ≤
        maximumBits := by
    exact
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans <|
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcalleeBits :
      maskedParityCalleeBits inputLength arity supportCode inputCode ≤
        callBits :=
    Nat.le_max_left _ _
  have hcallOne : 1 ≤ callBits :=
    (Nat.le_max_left _ _).trans hcalleeBits
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength arity context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput arity context)) =
        some (Nat.pair requestTree context) := by
    exact run_bits_mono
      (run_generatedBalancedRangeProgram inputLength arity context)
      hrangeBits
  have hcall :
      runNPOracleProgram (balancedCallProgram maskBitProgram) callBits
          (balancedCallFuel maskBitProgram (fun _ => maskBitFuel) requests)
          (initialNPOracleState inputLength requestTree) =
        some valueTree := by
    have hrun :=
      run_balancedCallProgram_from
        (callee := maskBitProgram) (maximumBits := callBits)
        inputLength requests (fun _ => maskBitFuel)
        (fun request => boolCode (maskBitValue request))
        (Nat.le_max_right _ _)
        (by
          intro request hrequest
          have hmem :
              natBitLength (Nat.unpair request).2 ∈
                requests.map fun candidate =>
                  natBitLength (Nat.unpair candidate).2 :=
            List.mem_map_of_mem hrequest
          have hbits :
              natBitLength (Nat.unpair request).2 ≤ callBits := by
            exact (le_foldr_max_of_mem hmem).trans <|
              (Nat.le_max_right _ _).trans hcalleeBits
          have hshape :
              ∃ index, request =
                balancedRangeRequestAtom inputLength index context := by
            have hrequests :
                requests =
                  balancedRangeRequestAtoms inputLength context 0 arity :=
              rfl
            rw [hrequests, balancedRangeRequestAtoms_eq_map_range]
              at hrequest
            rcases List.mem_map.mp hrequest with ⟨offset, _, hoffset⟩
            exact ⟨0 + offset, hoffset.symm⟩
          obtain ⟨index, hindex⟩ := hshape
          rw [hindex]
          rw [hindex] at hbits
          have hinput :
              natBitLength (maskBitInput index supportCode inputCode) ≤
                callBits := by
            simpa only [balancedRangeRequestAtom, Nat.unpair_pair,
              maskBitInput, context] using hbits
          have hlength :
              (Nat.unpair
                (balancedRangeRequestAtom inputLength index context)).1 =
                inputLength := by
            simp [balancedRangeRequestAtom]
          have htail :
              (Nat.unpair
                (balancedRangeRequestAtom inputLength index context)).2 =
                maskBitInput index supportCode inputCode := by
            simp [balancedRangeRequestAtom, maskBitInput, context]
          rw [hlength, htail, maskBitValue_atom]
          exact run_maskBitProgram inputLength index supportCode inputCode
            callBits hinput hcallOne)
    simpa only [valueTree, values, maskedParityValues, encodeBoolList,
      List.map_map, Function.comp_def, requestTree, requests] using hrun
  have hpreserve :
      runNPOracleProgram
          (preserveRightProgram (balancedCallProgram maskBitProgram))
          maximumBits
          (preserveRightFuel
            (balancedCallFuel maskBitProgram (fun _ => maskBitFuel) requests))
          (initialNPOracleState inputLength
            (Nat.pair requestTree context)) =
        some (Nat.pair valueTree context) := by
    exact run_bits_mono
      (run_preserveRightProgram (balancedCallProgram maskBitProgram)
        inputLength callBits
        (balancedCallFuel maskBitProgram (fun _ => maskBitFuel) requests)
        requestTree context valueTree hcall)
      hpreserveBits
  have hdrop :
      runNPOracleProgram dropRightProgram maximumBits 2
          (initialNPOracleState inputLength
            (Nat.pair valueTree context)) =
        some valueTree := by
    exact run_bits_mono
      (run_dropRightProgram inputLength valueTree context) hdropBits
  have hparity :
      runNPOracleProgram balancedBitParityProgram maximumBits
          (balancedBitParityFuel (values.map boolCode))
          (initialNPOracleState inputLength valueTree) =
        some (taggedParity (values.map boolCode)) := by
    exact run_bits_mono
      (run_balancedBitParityProgram inputLength (values.map boolCode))
      hparityBits
  have htail :
      runNPOracleProgram
          (linkPrograms dropRightProgram balancedBitParityProgram)
          maximumBits
          (maskedParityTailFuel inputLength arity supportCode inputCode)
          (initialNPOracleState inputLength
            (Nat.pair valueTree context)) =
        some (taggedParity (values.map boolCode)) :=
    run_linkPrograms hpositive hlengthBits hdrop hparity
  have hafter :
      runNPOracleProgram
          (linkPrograms
            (preserveRightProgram (balancedCallProgram maskBitProgram))
            (linkPrograms dropRightProgram balancedBitParityProgram))
          maximumBits
          (maskedParityAfterRangeFuel inputLength arity supportCode inputCode)
          (initialNPOracleState inputLength
            (Nat.pair requestTree context)) =
        some (taggedParity (values.map boolCode)) :=
    run_linkPrograms hpositive hlengthBits hpreserve htail
  have hrun := run_linkPrograms hpositive hlengthBits hrange hafter
  have houtput :
      taggedParity (values.map boolCode) =
        ((supportMaskBits supportCode
          (bitInputPrefixView arity inputCode)).foldl xor false).toNat := by
    have hcode : values.map boolCode = values.map Bool.toNat := rfl
    have hvalues :
        values =
          supportMaskBits supportCode (bitInputPrefixView arity inputCode) :=
      maskedParityValues_eq_supportMaskBits inputLength arity supportCode
        inputCode
    rw [hcode, taggedParity_boolToNat, hvalues]
  rw [← houtput]
  simpa only [maskedParityProgram, maskedParityFuel, context, requestTree,
    requests, valueTree, values, maximumBits] using hrun

end NearCubicWires.CaseTwoOccurrenceParityProgram
