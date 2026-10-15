import Proof.MachineModel.CanonicalBooleanizeProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalSupplierSupportCompressionProgram

/-!
# Canonical Boolean range aggregation

This module closes the generic controller tail used by supplier rows.  A
single statically selected callee is applied to the canonical requests
`0, ..., count - 1`; the balanced output tree is reduced in place to its true
leaf count while an opaque denominator context is preserved.  The callee is a
link-time program parameter, never a run-time callback, and the public machine
has no flat-list or full-cube fallback.
-/

namespace NearCubicWires.CanonicalBooleanRangeAggregationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanizeProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-- The exact callable atoms consumed by the fixed balanced-call controller. -/
def fixedBooleanRangeRequests
    (inputLength count context : ℕ) : List ℕ :=
  balancedRangeRequestAtoms inputLength context 0 count

def fixedBooleanRangeValues
    (inputLength count context : ℕ) (value : ℕ → Bool) : List Bool :=
  (fixedBooleanRangeRequests inputLength count context).map value

/-- The aggregation tail preserves the caller's denominator context. -/
def fixedBooleanRangeAggregationOutput
    (inputLength count context : ℕ) (value : ℕ → Bool) : ℕ :=
  Nat.pair
    (nonzeroSupportCount
      (fixedBooleanRangeValues inputLength count context value))
    context

/-! ## Canonical component packing -/

/-- The aggregation controller naturally returns a native pair.  This sole
adapter converts that pair into the two-field canonical tagged record consumed
by `canonicalRatioPackerProgram`; it does not compute or receive a final ratio
code. -/
def canonicalRatioComponentEncoderProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .encodeNat 2 4 3
  , .encodeNat 3 5 4
  , .set 6 0 5
  , .set 9 1 6
  , .pair 5 6 7 7
  , .pair 9 7 7 8
  , .pair 4 7 8 9
  , .pair 9 8 0 10
  , .halt 0
  ]

def canonicalRatioComponentEncoderOutput
    (numerator denominatorTail : ℕ) : ℕ :=
  encodeTaggedList [encodeNat numerator, encodeNat denominatorTail]

def canonicalRatioComponentEncoderBits
    (numerator denominatorTail : ℕ) : ℕ :=
  natBitLength <|
    max (Nat.pair numerator denominatorTail)
      (canonicalRatioComponentEncoderOutput numerator denominatorTail) + 1

@[simp] theorem canonicalRatioComponentEncoderProgram_oracleFree :
    OracleFree canonicalRatioComponentEncoderProgram := by
  rfl

theorem run_canonicalRatioComponentEncoderProgram
    (inputLength numerator denominatorTail : ℕ) :
    runNPOracleProgram canonicalRatioComponentEncoderProgram
        (canonicalRatioComponentEncoderBits numerator denominatorTail) 11
        (initialNPOracleState inputLength
          (Nat.pair numerator denominatorTail)) =
      some
        (canonicalRatioComponentEncoderOutput
          numerator denominatorTail) := by
  let raw := Nat.pair numerator denominatorTail
  let numeratorCode := encodeNat numerator
  let denominatorCode := encodeNat denominatorTail
  let denominatorPayload := Nat.pair denominatorCode 0
  let denominatorList := Nat.pair 1 denominatorPayload
  let payload := Nat.pair numeratorCode denominatorList
  let output := Nat.pair 1 payload
  let bound := max raw output + 1
  let maximumBits :=
    canonicalRatioComponentEncoderBits numerator denominatorTail
  have hbound : natBitLength bound = maximumBits := by
    simp [bound, maximumBits, canonicalRatioComponentEncoderBits,
      raw, output, canonicalRatioComponentEncoderOutput,
      payload, denominatorList, denominatorPayload, numeratorCode,
      denominatorCode, encodeTaggedList]
  have bits_of_le {candidate : ℕ} (hcandidate : candidate ≤ bound) :
      natBitLength candidate ≤ maximumBits := by
    rw [← hbound]
    exact natBitLength_mono hcandidate
  have hraw : natBitLength raw ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hnumerator : natBitLength numerator ≤ maximumBits := by
    exact (natBitLength_mono (Nat.left_le_pair numerator denominatorTail)).trans
      hraw
  have hdenominator : natBitLength denominatorTail ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair numerator denominatorTail)).trans hraw
  have hzero : natBitLength 0 ≤ maximumBits := by
    exact natBitLength_mono (Nat.zero_le raw) |>.trans hraw
  have hone : natBitLength 1 ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.left_le_pair 1 payload)).trans houtput
  have hpayload : natBitLength payload ≤ maximumBits := by
    exact
      (natBitLength_mono (Nat.right_le_pair 1 payload)).trans houtput
  have hnumeratorCode :
      natBitLength numeratorCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair numeratorCode denominatorList)).trans hpayload
  have hdenominatorList :
      natBitLength denominatorList ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair numeratorCode denominatorList)).trans hpayload
  have hdenominatorPayload :
      natBitLength denominatorPayload ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.right_le_pair 1 denominatorPayload)).trans hdenominatorList
  have hdenominatorCode :
      natBitLength denominatorCode ≤ maximumBits := by
    exact
      (natBitLength_mono
        (Nat.left_le_pair denominatorCode 0)).trans hdenominatorPayload
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairLeft_instruction (value := numerator)
    (by rfl) rfl (by simp [initialNPOracleState]) hnumerator]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairRight_instruction (value := denominatorTail)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    hdenominator]
  rw [show 9 = 8 + 1 by omega]
  rw [run_encodeNat_instruction (value := numerator)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    hnumeratorCode]
  rw [show 8 = 7 + 1 by omega]
  rw [run_encodeNat_instruction (value := denominatorTail)
    (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump])
    hdenominatorCode]
  rw [show 7 = 6 + 1 by omega]
  rw [run_set_instruction (value := 0)
    (by rfl) rfl hzero]
  rw [show 6 = 5 + 1 by omega]
  rw [run_set_instruction (value := 1)
    (by rfl) rfl hone]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := denominatorPayload)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump, denominatorPayload, denominatorCode])
    hdenominatorPayload]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := denominatorList)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        denominatorList, denominatorPayload])
    hdenominatorList]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := payload)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, payload,
        numeratorCode, denominatorList])
    hpayload]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output, payload])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-- One production controller: canonical range generation, balanced calls,
balanced Boolean count, and no alternate materialization path. -/
def fixedBooleanRangeAggregationProgram
    (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms generatedBalancedRangeProgram <|
    linkPrograms
      (preserveRightProgram (balancedCallProgram callee)) <|
        linkPrograms swapPairProgram balancedBoolCountProgram

def fixedBooleanRangeCallBits
    (calleeBits inputLength count context : ℕ)
    (value : ℕ → Bool) : ℕ :=
  max calleeBits <|
    balancedCallRequiredBits
      (fun request => boolCode (value request))
      (fixedBooleanRangeRequests inputLength count context)

def fixedBooleanRangeMappedBits
    (calleeBits inputLength count context : ℕ)
    (value : ℕ → Bool) : ℕ :=
  preserveRightBits
    (fixedBooleanRangeCallBits
      calleeBits inputLength count context value)
    (encodeBalancedList
      (fixedBooleanRangeRequests inputLength count context))
    context
    (encodeBoolList
      (fixedBooleanRangeValues inputLength count context value))

/-- Exact maximum width of the four linked stages.  Published estimators may
replace it by any proved public polynomial upper bound. -/
def fixedBooleanRangeAggregationBits
    (calleeBits inputLength count context : ℕ)
    (value : ℕ → Bool) : ℕ :=
  max (natBitLength inputLength) <|
    max
      (generatedBalancedRangeRequiredBits inputLength count context) <|
      max
        (fixedBooleanRangeMappedBits
          calleeBits inputLength count context value) <|
        max
          (swapPairBits
            (encodeBoolList
              (fixedBooleanRangeValues inputLength count context value))
            context)
          (balancedBoolCountBits inputLength context
            (fixedBooleanRangeValues inputLength count context value))

theorem inputLength_bits_le_fixedBooleanRangeAggregationBits
    (calleeBits inputLength count context : ℕ)
    (value : ℕ → Bool) :
    natBitLength inputLength ≤
      fixedBooleanRangeAggregationBits
        calleeBits inputLength count context value :=
  Nat.le_max_left _ _

def fixedBooleanRangeCallFuel
    (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (inputLength count context : ℕ) : ℕ :=
  balancedCallFuel callee calleeFuel
    (fixedBooleanRangeRequests inputLength count context)

def fixedBooleanRangeMappedFuel
    (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (inputLength count context : ℕ) : ℕ :=
  preserveRightFuel <|
    fixedBooleanRangeCallFuel callee calleeFuel
      inputLength count context

def fixedBooleanRangeTailFuel
    (inputLength count context : ℕ) (value : ℕ → Bool) : ℕ :=
  linkFuel balancedBoolCountProgram 4 <|
    balancedBoolCountFuel
      (fixedBooleanRangeValues inputLength count context value)

def fixedBooleanRangeAfterGenerationFuel
    (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (inputLength count context : ℕ)
    (value : ℕ → Bool) : ℕ :=
  linkFuel (linkPrograms swapPairProgram balancedBoolCountProgram)
    (fixedBooleanRangeMappedFuel callee calleeFuel
      inputLength count context)
    (fixedBooleanRangeTailFuel inputLength count context value)

def fixedBooleanRangeAggregationFuel
    (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (inputLength count context : ℕ)
    (value : ℕ → Bool) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram (balancedCallProgram callee))
      (linkPrograms swapPairProgram balancedBoolCountProgram))
    (generatedBalancedRangeFuel inputLength count context)
    (fixedBooleanRangeAfterGenerationFuel callee calleeFuel
      inputLength count context value)

theorem fixedBooleanRangeAggregationProgram_oracleFree
    (callee : NPOracleProgram) (hcallee : OracleFree callee) :
    OracleFree (fixedBooleanRangeAggregationProgram callee) := by
  apply oracleFree_linkPrograms generatedBalancedRangeProgram_oracleFree
  apply oracleFree_linkPrograms
  · exact preserveRightProgram_oracleFree
      (balancedCallProgram callee)
      (balancedCallProgram_oracleFree hcallee)
  · exact oracleFree_linkPrograms swapPairProgram_oracleFree
      balancedBoolCountProgram_oracleFree

theorem run_fixedBooleanRangeAggregationProgram
    (callee : NPOracleProgram)
    (calleeBits inputLength count context : ℕ)
    (calleeFuel : ℕ → ℕ) (value : ℕ → Bool)
    (hexec : ∀ request,
      request ∈ fixedBooleanRangeRequests inputLength count context →
      runNPOracleProgram callee calleeBits (calleeFuel request)
          (initialNPOracleState
            (Nat.unpair request).1 (Nat.unpair request).2) =
        some (boolCode (value request))) :
    runNPOracleProgram
        (fixedBooleanRangeAggregationProgram callee)
        (fixedBooleanRangeAggregationBits
          calleeBits inputLength count context value)
        (fixedBooleanRangeAggregationFuel callee calleeFuel
          inputLength count context value)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count context)) =
      some
        (fixedBooleanRangeAggregationOutput
          inputLength count context value) := by
  let requests :=
    fixedBooleanRangeRequests inputLength count context
  let values :=
    fixedBooleanRangeValues inputLength count context value
  let requestTree := encodeBalancedList requests
  let valueTree := encodeBoolList values
  let callBits :=
    fixedBooleanRangeCallBits
      calleeBits inputLength count context value
  let mappedBits :=
    fixedBooleanRangeMappedBits
      calleeBits inputLength count context value
  let maximumBits :=
    fixedBooleanRangeAggregationBits
      calleeBits inputLength count context value
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans (Nat.le_max_left _ _)
  have hinputLength : natBitLength inputLength ≤ maximumBits :=
    Nat.le_max_left _ _
  have hrangeBits :
      generatedBalancedRangeRequiredBits inputLength count context ≤
        maximumBits := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hmappedBits : mappedBits ≤ maximumBits := by
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hswapBits :
      swapPairBits valueTree context ≤ maximumBits := by
    dsimp only [maximumBits,
      fixedBooleanRangeAggregationBits]
    exact (Nat.le_max_left _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hcountBits :
      balancedBoolCountBits inputLength context values ≤
        maximumBits := by
    dsimp only [maximumBits,
      fixedBooleanRangeAggregationBits]
    exact (Nat.le_max_right _ _).trans <|
      (Nat.le_max_right _ _).trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hrange :
      runNPOracleProgram generatedBalancedRangeProgram maximumBits
          (generatedBalancedRangeFuel inputLength count context)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count context)) =
        some (Nat.pair requestTree context) := by
    apply run_bits_mono
      (run_generatedBalancedRangeProgram inputLength count context)
      hrangeBits
  have hcall :
      runNPOracleProgram (balancedCallProgram callee) callBits
          (fixedBooleanRangeCallFuel callee calleeFuel
            inputLength count context)
          (initialNPOracleState inputLength requestTree) =
        some valueTree := by
    have hrun :=
      run_balancedCallProgram_from
        (callee := callee) (maximumBits := callBits)
        inputLength requests calleeFuel
        (fun request => boolCode (value request))
        (Nat.le_max_right _ _)
        (by
          intro request hrequest
          exact run_bits_mono
            (hexec request (by simpa [requests] using hrequest))
            (Nat.le_max_left _ _))
    simpa [fixedBooleanRangeCallFuel, callBits, requestTree,
      valueTree, requests, values, fixedBooleanRangeValues,
      encodeBoolList, List.map_map, Function.comp_def] using hrun
  have hmapped :
      runNPOracleProgram
          (preserveRightProgram (balancedCallProgram callee))
          maximumBits
          (fixedBooleanRangeMappedFuel callee calleeFuel
            inputLength count context)
          (initialNPOracleState inputLength
            (Nat.pair requestTree context)) =
        some (Nat.pair valueTree context) := by
    apply run_bits_mono
      (run_preserveRightProgram
        (balancedCallProgram callee)
        inputLength callBits
        (fixedBooleanRangeCallFuel callee calleeFuel
          inputLength count context)
        requestTree context valueTree hcall)
      hmappedBits
  have hswap :
      runNPOracleProgram swapPairProgram maximumBits 4
          (initialNPOracleState inputLength
            (Nat.pair valueTree context)) =
        some (Nat.pair context valueTree) := by
    exact run_bits_mono
      (run_swapPairProgram inputLength valueTree context)
      hswapBits
  have hcount :
      runNPOracleProgram balancedBoolCountProgram maximumBits
          (balancedBoolCountFuel values)
          (initialNPOracleState inputLength
            (Nat.pair context valueTree)) =
        some (Nat.pair (nonzeroSupportCount values) context) := by
    exact run_bits_mono
      (run_balancedBoolCountProgram inputLength context values)
      hcountBits
  have htail :
      runNPOracleProgram
          (linkPrograms swapPairProgram balancedBoolCountProgram)
          maximumBits
          (fixedBooleanRangeTailFuel inputLength count context value)
          (initialNPOracleState inputLength
            (Nat.pair valueTree context)) =
        some (Nat.pair (nonzeroSupportCount values) context) := by
    exact run_linkPrograms hpositive hinputLength hswap hcount
  have hafter :
      runNPOracleProgram
          (linkPrograms
            (preserveRightProgram (balancedCallProgram callee))
            (linkPrograms swapPairProgram balancedBoolCountProgram))
          maximumBits
          (fixedBooleanRangeAfterGenerationFuel callee calleeFuel
            inputLength count context value)
          (initialNPOracleState inputLength
            (Nat.pair requestTree context)) =
        some (Nat.pair (nonzeroSupportCount values) context) := by
    exact run_linkPrograms hpositive hinputLength hmapped htail
  have hrun :=
    run_linkPrograms hpositive hinputLength hrange hafter
  simpa [fixedBooleanRangeAggregationProgram,
    fixedBooleanRangeAggregationFuel,
    fixedBooleanRangeAggregationOutput, requests, values, maximumBits]
    using hrun

/-! ## Closed aggregation-component program -/

/-- Public range context.  The denominator is retained for the final ratio
component while `rowContext` is opaque metadata consumed only by the statically
linked row callee. -/
def fixedBooleanRangeComponentContext
    (denominatorTail rowContext : ℕ) : ℕ :=
  Nat.pair denominatorTail rowContext

/-- Remove row-only metadata after the Boolean count.  This is the sole
transition from `pair(numerator, pair(denominatorTail, rowContext))` to the
native pair consumed by the canonical component encoder. -/
def canonicalAggregationContextProjectionProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .pair 2 4 0 4
  , .halt 0
  ]

def canonicalAggregationContextProjectionInput
    (numerator denominatorTail rowContext : ℕ) : ℕ :=
  Nat.pair numerator
    (fixedBooleanRangeComponentContext denominatorTail rowContext)

def canonicalAggregationContextProjectionOutput
    (numerator denominatorTail : ℕ) : ℕ :=
  Nat.pair numerator denominatorTail

def canonicalAggregationContextProjectionBits
    (numerator denominatorTail rowContext : ℕ) : ℕ :=
  natBitLength <|
    max
      (canonicalAggregationContextProjectionInput
        numerator denominatorTail rowContext)
      (canonicalAggregationContextProjectionOutput
        numerator denominatorTail) + 1

@[simp] theorem canonicalAggregationContextProjectionProgram_oracleFree :
    OracleFree canonicalAggregationContextProjectionProgram := by
  rfl

theorem run_canonicalAggregationContextProjectionProgram
    (inputLength numerator denominatorTail rowContext : ℕ) :
    runNPOracleProgram canonicalAggregationContextProjectionProgram
        (canonicalAggregationContextProjectionBits
          numerator denominatorTail rowContext)
        5
        (initialNPOracleState inputLength
          (canonicalAggregationContextProjectionInput
            numerator denominatorTail rowContext)) =
      some
        (canonicalAggregationContextProjectionOutput
          numerator denominatorTail) := by
  let context :=
    fixedBooleanRangeComponentContext denominatorTail rowContext
  let input :=
    canonicalAggregationContextProjectionInput
      numerator denominatorTail rowContext
  let output :=
    canonicalAggregationContextProjectionOutput numerator denominatorTail
  let bound := max input output + 1
  let maximumBits :=
    canonicalAggregationContextProjectionBits
      numerator denominatorTail rowContext
  have hmaximumBits : natBitLength bound = maximumBits := by
    rfl
  have bits_of_le {value : ℕ} (hvalue : value ≤ bound) :
      natBitLength value ≤ maximumBits := by
    rw [← hmaximumBits]
    exact natBitLength_mono hvalue
  have hinput : natBitLength input ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_left _ _).trans (Nat.le_add_right _ _)
  have houtput : natBitLength output ≤ maximumBits := by
    apply bits_of_le
    exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  have hnumerator : natBitLength numerator ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair numerator context)).trans hinput
  have hcontext : natBitLength context ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair numerator context)).trans hinput
  have hdenominator : natBitLength denominatorTail ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair denominatorTail rowContext)).trans hcontext
  rw [show 5 = 4 + 1 by omega]
  rw [run_unpairLeft_instruction (value := numerator)
    (by rfl) rfl
    (by
      simp [initialNPOracleState,
        canonicalAggregationContextProjectionInput])
    hnumerator]
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairRight_instruction (value := context)
    (by rfl) rfl
    (by
      simp [initialNPOracleState, NPOracleState.write,
        NPOracleState.jump,
        canonicalAggregationContextProjectionInput, context])
    hcontext]
  rw [show 3 = 2 + 1 by omega]
  rw [run_unpairLeft_instruction (value := denominatorTail)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, context,
        fixedBooleanRangeComponentContext])
    hdenominator]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := output)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, output,
        canonicalAggregationContextProjectionOutput])
    houtput]
  exact run_halt_instruction (fuel := 0) (value := output)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, output])
    houtput

/-- Canonical tagged component returned at the published artifact boundary. -/
def fixedBooleanRangeComponentOutput
    (inputLength count denominatorTail rowContext : ℕ)
    (value : ℕ → Bool) : ℕ :=
  canonicalRatioComponentEncoderOutput
    (nonzeroSupportCount
      (fixedBooleanRangeValues inputLength count
        (fixedBooleanRangeComponentContext denominatorTail rowContext) value))
    denominatorTail

/-- The complete reusable controller tail.  A production row callee is linked
once, and the result already has the exact component ABI expected by the
shared ratio packer. -/
def fixedBooleanRangeComponentProgram
    (callee : NPOracleProgram) : NPOracleProgram :=
  linkPrograms (fixedBooleanRangeAggregationProgram callee) <|
    linkPrograms canonicalAggregationContextProjectionProgram
      canonicalRatioComponentEncoderProgram

def fixedBooleanRangeComponentBits
    (calleeBits inputLength count denominatorTail rowContext : ℕ)
    (value : ℕ → Bool) : ℕ :=
  let context :=
    fixedBooleanRangeComponentContext denominatorTail rowContext
  let numerator :=
    nonzeroSupportCount
      (fixedBooleanRangeValues inputLength count context value)
  max
    (fixedBooleanRangeAggregationBits
      calleeBits inputLength count context value) <|
    max
      (canonicalAggregationContextProjectionBits
        numerator denominatorTail rowContext)
      (canonicalRatioComponentEncoderBits numerator denominatorTail)

def fixedBooleanRangeComponentFuel
    (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ)
    (inputLength count denominatorTail rowContext : ℕ)
    (value : ℕ → Bool) : ℕ :=
  linkFuel
    (linkPrograms canonicalAggregationContextProjectionProgram
      canonicalRatioComponentEncoderProgram)
    (fixedBooleanRangeAggregationFuel callee calleeFuel
      inputLength count
        (fixedBooleanRangeComponentContext denominatorTail rowContext) value)
    (linkFuel canonicalRatioComponentEncoderProgram 5 11)

theorem fixedBooleanRangeComponentProgram_oracleFree
    (callee : NPOracleProgram) (hcallee : OracleFree callee) :
    OracleFree (fixedBooleanRangeComponentProgram callee) := by
  apply oracleFree_linkPrograms
  · exact fixedBooleanRangeAggregationProgram_oracleFree callee hcallee
  · exact oracleFree_linkPrograms
      canonicalAggregationContextProjectionProgram_oracleFree
      canonicalRatioComponentEncoderProgram_oracleFree

set_option maxHeartbeats 600000 in
-- Elaborating the nested linked controller trace dominates this final handoff.
theorem run_fixedBooleanRangeComponentProgram
    (callee : NPOracleProgram)
    (calleeBits inputLength count denominatorTail rowContext : ℕ)
    (calleeFuel : ℕ → ℕ) (value : ℕ → Bool)
    (hexec : ∀ request,
      request ∈
          fixedBooleanRangeRequests
            inputLength count
              (fixedBooleanRangeComponentContext
                denominatorTail rowContext) →
      runNPOracleProgram callee calleeBits (calleeFuel request)
          (initialNPOracleState
            (Nat.unpair request).1 (Nat.unpair request).2) =
        some (boolCode (value request))) :
    runNPOracleProgram
        (fixedBooleanRangeComponentProgram callee)
        (fixedBooleanRangeComponentBits
          calleeBits inputLength count denominatorTail rowContext value)
        (fixedBooleanRangeComponentFuel callee calleeFuel
          inputLength count denominatorTail rowContext value)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count
            (fixedBooleanRangeComponentContext
              denominatorTail rowContext))) =
      some
        (fixedBooleanRangeComponentOutput
          inputLength count denominatorTail rowContext value) := by
  let context :=
    fixedBooleanRangeComponentContext denominatorTail rowContext
  let values :=
    fixedBooleanRangeValues
      inputLength count context value
  let numerator := nonzeroSupportCount values
  let aggregationBits :=
    fixedBooleanRangeAggregationBits
      calleeBits inputLength count context value
  let projectionBits :=
    canonicalAggregationContextProjectionBits
      numerator denominatorTail rowContext
  let encoderBits :=
    canonicalRatioComponentEncoderBits numerator denominatorTail
  let maximumBits :=
    fixedBooleanRangeComponentBits
      calleeBits inputLength count denominatorTail rowContext value
  have haggregationBits : aggregationBits ≤ maximumBits :=
    Nat.le_max_left _ _
  have hprojectionBits : projectionBits ≤ maximumBits :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hencoderBits : encoderBits ≤ maximumBits :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hinputLength : natBitLength inputLength ≤ maximumBits := by
    exact
      (inputLength_bits_le_fixedBooleanRangeAggregationBits
        calleeBits inputLength count context value).trans
          haggregationBits
  have hpositive : 1 ≤ maximumBits := by
    exact (show 1 ≤ natBitLength inputLength by
      unfold natBitLength
      omega).trans hinputLength
  have haggregation :
      runNPOracleProgram
          (fixedBooleanRangeAggregationProgram callee)
          maximumBits
          (fixedBooleanRangeAggregationFuel callee calleeFuel
            inputLength count context value)
          (initialNPOracleState inputLength
            (generatedBalancedRangeInput count context)) =
        some (Nat.pair numerator context) := by
    have hrun :=
      run_bits_mono
        (run_fixedBooleanRangeAggregationProgram
          callee calleeBits inputLength count context
          calleeFuel value hexec)
        haggregationBits
    simpa only [fixedBooleanRangeAggregationOutput, values, numerator]
      using hrun
  have hprojection :
      runNPOracleProgram canonicalAggregationContextProjectionProgram
          maximumBits 5
          (initialNPOracleState inputLength
            (Nat.pair numerator context)) =
        some (Nat.pair numerator denominatorTail) := by
    exact run_bits_mono
      (run_canonicalAggregationContextProjectionProgram
        inputLength numerator denominatorTail rowContext)
      hprojectionBits
  have hencode :
      runNPOracleProgram canonicalRatioComponentEncoderProgram
          maximumBits 11
          (initialNPOracleState inputLength
            (Nat.pair numerator denominatorTail)) =
        some
          (canonicalRatioComponentEncoderOutput
            numerator denominatorTail) := by
    exact run_bits_mono
      (run_canonicalRatioComponentEncoderProgram
        inputLength numerator denominatorTail)
      hencoderBits
  have htail :
      runNPOracleProgram
          (linkPrograms canonicalAggregationContextProjectionProgram
            canonicalRatioComponentEncoderProgram)
          maximumBits
          (linkFuel canonicalRatioComponentEncoderProgram 5 11)
          (initialNPOracleState inputLength
            (Nat.pair numerator context)) =
        some
          (canonicalRatioComponentEncoderOutput
            numerator denominatorTail) :=
    run_linkPrograms hpositive hinputLength hprojection hencode
  have hrun :=
    run_linkPrograms hpositive hinputLength haggregation htail
  simpa [fixedBooleanRangeComponentProgram,
    fixedBooleanRangeComponentFuel,
    fixedBooleanRangeComponentOutput, values, numerator, maximumBits,
    context]
    using hrun

/-! ## Signed-row Booleanization boundary -/

theorem run_fixedBooleanizedIntRangeComponentProgram
    (source : NPOracleProgram)
    (sourceBits inputLength count denominatorTail rowContext : ℕ)
    (sourceFuel : ℕ → ℕ) (sourceValue : ℕ → ℤ)
    (hsourceBits : 1 ≤ sourceBits)
    (hinputLength : natBitLength inputLength ≤ sourceBits)
    (hexec : ∀ request,
      request ∈
          fixedBooleanRangeRequests
            inputLength count
              (fixedBooleanRangeComponentContext
                denominatorTail rowContext) →
      runNPOracleProgram source sourceBits (sourceFuel request)
          (initialNPOracleState
            (Nat.unpair request).1 (Nat.unpair request).2) =
        some (encodeInt (sourceValue request))) :
    let value : ℕ → Bool :=
      fun request => decide (sourceValue request ≠ 0)
    runNPOracleProgram
        (fixedBooleanRangeComponentProgram (booleanizedProgram source))
        (fixedBooleanRangeComponentBits
          sourceBits inputLength count denominatorTail rowContext value)
        (fixedBooleanRangeComponentFuel (booleanizedProgram source)
          (fun request => booleanizedFuel (sourceFuel request))
          inputLength count denominatorTail rowContext value)
        (initialNPOracleState inputLength
          (generatedBalancedRangeInput count
            (fixedBooleanRangeComponentContext
              denominatorTail rowContext))) =
      some
        (fixedBooleanRangeComponentOutput
          inputLength count denominatorTail rowContext value) := by
  dsimp only
  apply run_fixedBooleanRangeComponentProgram
  intro request hrequest
  apply run_booleanizedProgram_encodeInt hsourceBits
  · rw [fixedBooleanRangeRequests,
      balancedRangeRequestAtoms_eq_map_range] at hrequest
    rcases List.mem_map.mp hrequest with ⟨offset, _, rfl⟩
    simpa [balancedRangeRequestAtom] using hinputLength
  · exact hexec request hrequest

/-! ## Smallest pre-contraction witness -/

def binarySignedTableProgram
    (zeroValue oneValue : ℤ) : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .branchZero 2 2 3
  , .set 0 (encodeInt zeroValue) 4
  , .set 0 (encodeInt oneValue) 4
  , .halt 0
  ]

@[simp] theorem binarySignedTableProgram_oracleFree
    (zeroValue oneValue : ℤ) :
    OracleFree (binarySignedTableProgram zeroValue oneValue) := by
  rfl

/-- One width shared by both q=1 executions.  The leading `1` covers both
canonical indices, while the remaining maxima cover the signed outputs. -/
def binarySignedTableBits (zeroValue oneValue : ℤ) : ℕ :=
  max 1
    (max (natBitLength (encodeInt zeroValue))
      (natBitLength (encodeInt oneValue)))

def binarySignedTableValue
    (zeroValue oneValue : ℤ) (request : ℕ) : ℤ :=
  if (Nat.unpair (Nat.unpair request).2).1 = 0 then
    zeroValue
  else
    oneValue

theorem run_binarySignedTableProgram
    (zeroValue oneValue : ℤ) (inputLength index context : ℕ)
    (hindex : index < 2) :
    runNPOracleProgram
        (binarySignedTableProgram zeroValue oneValue)
        (binarySignedTableBits zeroValue oneValue) 4
        (initialNPOracleState inputLength (Nat.pair index context)) =
      some (encodeInt (if index = 0 then zeroValue else oneValue)) := by
  have hindexBits :
      natBitLength index ≤ binarySignedTableBits zeroValue oneValue := by
    have : natBitLength index ≤ 1 := by
      interval_cases index <;> simp [natBitLength]
    exact this.trans (Nat.le_max_left _ _)
  have hzeroBits :
      natBitLength (encodeInt zeroValue) ≤
        binarySignedTableBits zeroValue oneValue :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have honeBits :
      natBitLength (encodeInt oneValue) ≤
        binarySignedTableBits zeroValue oneValue :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  rw [show 4 = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (fuel := 3) (value := index)
    (by rfl) rfl
    (by simp [initialNPOracleState])
    hindexBits]
  rw [show 3 = 2 + 1 by omega]
  rw [run_branchZero_instruction (fuel := 2) (by rfl) rfl]
  rw [show
    ((((initialNPOracleState inputLength (Nat.pair index context)).write
        2 index).jump 1).registers 2) = index by
      simp [NPOracleState.write, NPOracleState.jump]]
  by_cases hzero : index = 0
  · rw [if_pos hzero]
    rw [show 2 = 1 + 1 by omega]
    rw [run_set_instruction (fuel := 1) (register := 0)
      (value := encodeInt zeroValue) (next := 4)
      (by rfl) rfl hzeroBits]
    simp [runNPOracleProgram, binarySignedTableProgram,
      NPOracleState.write, NPOracleState.jump, hzeroBits, hzero]
  · rw [if_neg hzero]
    rw [show 2 = 1 + 1 by omega]
    rw [run_set_instruction (fuel := 1) (register := 0)
      (value := encodeInt oneValue) (next := 4)
      (by rfl) rfl honeBits]
    simp [runNPOracleProgram, binarySignedTableProgram,
      NPOracleState.write, NPOracleState.jump, honeBits, hzero]

theorem run_qOneBinarySignedRangeComponentProgram
    (zeroValue oneValue : ℤ) (denominatorTail rowContext : ℕ) :
    let sourceValue :=
      binarySignedTableValue zeroValue oneValue
    let value : ℕ → Bool :=
      fun request => decide (sourceValue request ≠ 0)
    runNPOracleProgram
        (fixedBooleanRangeComponentProgram
          (booleanizedProgram
            (binarySignedTableProgram zeroValue oneValue)))
        (fixedBooleanRangeComponentBits
          (binarySignedTableBits zeroValue oneValue)
          1 2 denominatorTail rowContext value)
        (fixedBooleanRangeComponentFuel
          (booleanizedProgram
            (binarySignedTableProgram zeroValue oneValue))
          (fun _ => booleanizedFuel 4)
          1 2 denominatorTail rowContext value)
        (initialNPOracleState 1
          (generatedBalancedRangeInput 2
            (fixedBooleanRangeComponentContext
              denominatorTail rowContext))) =
      some
        (fixedBooleanRangeComponentOutput
          1 2 denominatorTail rowContext value) := by
  dsimp only
  apply run_fixedBooleanizedIntRangeComponentProgram
      (source := binarySignedTableProgram zeroValue oneValue)
      (sourceBits := binarySignedTableBits zeroValue oneValue)
      (inputLength := 1)
      (count := 2)
      (denominatorTail := denominatorTail)
      (rowContext := rowContext)
      (sourceFuel := fun _ => 4)
      (sourceValue := binarySignedTableValue zeroValue oneValue)
  · unfold binarySignedTableBits
    omega
  · unfold binarySignedTableBits
    simp [natBitLength]
  · intro request hrequest
    have hcases :
        request =
            balancedRangeRequestAtom 1 0
              (fixedBooleanRangeComponentContext denominatorTail rowContext) ∨
          request =
            balancedRangeRequestAtom 1 1
              (fixedBooleanRangeComponentContext
                denominatorTail rowContext) := by
      simpa only [fixedBooleanRangeRequests, balancedRangeRequestAtoms,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        Nat.zero_add] using hrequest
    rcases hcases with rfl | rfl
    · simpa [balancedRangeRequestAtom, binarySignedTableValue] using
        run_binarySignedTableProgram zeroValue oneValue 1 0
          (fixedBooleanRangeComponentContext denominatorTail rowContext)
          (by omega)
    · simpa [balancedRangeRequestAtom, binarySignedTableValue] using
        run_binarySignedTableProgram zeroValue oneValue 1 1
          (fixedBooleanRangeComponentContext denominatorTail rowContext)
          (by omega)

end NearCubicWires.CanonicalBooleanRangeAggregationProgram
