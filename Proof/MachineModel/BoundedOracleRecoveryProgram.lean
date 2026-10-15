import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.Foundations.DynamicCNFBuilder
import Proof.MachineModel.StructuralClauseStreamProgram

/-!
# Executable bounded-oracle recovery

This module owns the public request syntax and the fixed-program boundary for
Appendix C.12 recovery.  Requests contain only the original input, the circuit
bound, and the requested description coordinate.  In particular, no circuit,
CNF, SAT answer, semantic verifier, or recovery callback is accepted as input.

The structural-CNF controller is intentionally assembled from the published
fixed PCP runners and the shared `DynamicCNFBuilder`/zero-first SAT reducer.
Keeping the request codec here makes that trust boundary independently
auditable before the larger linked controller is introduced below.
-/

namespace NearCubicWires.BoundedOracleRecoveryProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalSATSelfReduction
open NearCubicWires.CircuitInputCNF
open NearCubicWires.DynamicCNFBuilder
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-- The sole runtime request for one recovered description bit.  `inputArity`
is supplied in interpreter register one; the remaining fields occupy register
zero in canonical structural syntax. -/
structure BoundedOracleRecoveryRequest where
  inputArity : ℕ
  input : BitInput inputArity
  circuitBound : ℕ
  coordinate : ℕ

def BoundedOracleRecoveryRequest.length
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  request.inputArity

/-- Canonical request body.  Unary fields are structural loop cursors rather
than raw machine naturals, so every variable-length loop has a unique external
representation that the weak machine can consume by unpairing. -/
def BoundedOracleRecoveryRequest.code
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  Nat.pair (encodeBitInput request.input) <|
    Nat.pair (encodeUnary request.circuitBound)
      (encodeUnary request.coordinate)

def requestInputOfCode (inputArity inputCode : ℕ) :
    BitInput inputArity :=
  fun bit => inputCode.testBit bit.val

@[simp] theorem requestInputOfCode_encodeBitInput
    {inputArity : ℕ} (input : BitInput inputArity) :
    requestInputOfCode inputArity (encodeBitInput input) = input := by
  funext bit
  unfold requestInputOfCode
  rw [encodeBitInput_eq_ofBits]
  exact Nat.testBit_ofBits_lt input bit.val bit.isLt

/-- Partial public decoder.  The final exact re-encoding check rejects high
input bits and every noncanonical unary spelling, instead of silently
normalizing malformed requests into the trusted runtime path. -/
def decodeBoundedOracleRecoveryRequest
    (inputArity code : ℕ) : Option BoundedOracleRecoveryRequest := do
  let root := Nat.unpair code
  let fields := Nat.unpair root.2
  let circuitBound ← decodeUnary fields.1
  let coordinate ← decodeUnary fields.2
  let request : BoundedOracleRecoveryRequest :=
    { inputArity
      input := requestInputOfCode inputArity root.1
      circuitBound
      coordinate }
  if request.code = code then some request else none

@[simp] theorem decodeBoundedOracleRecoveryRequest_encode
    (request : BoundedOracleRecoveryRequest) :
    decodeBoundedOracleRecoveryRequest request.inputArity request.code =
      some request := by
  cases request with
  | mk inputArity input circuitBound coordinate =>
      simp [decodeBoundedOracleRecoveryRequest,
        BoundedOracleRecoveryRequest.code,
        requestInputOfCode_encodeBitInput]

theorem BoundedOracleRecoveryRequest.code_of_decode
    {inputArity code : ℕ} {request : BoundedOracleRecoveryRequest}
    (hdecode :
      decodeBoundedOracleRecoveryRequest inputArity code = some request) :
    request.code = code := by
  generalize hbound :
    decodeUnary (Nat.unpair (Nat.unpair code).2).1 = boundOption at hdecode
  cases boundOption with
  | none =>
      simp [decodeBoundedOracleRecoveryRequest, hbound] at hdecode
  | some circuitBound =>
      generalize hcoordinate :
        decodeUnary (Nat.unpair (Nat.unpair code).2).2 =
          coordinateOption at hdecode
      cases coordinateOption with
      | none =>
          simp [decodeBoundedOracleRecoveryRequest, hbound,
            hcoordinate] at hdecode
      | some coordinate =>
          let candidate : BoundedOracleRecoveryRequest :=
            { inputArity
              input :=
                requestInputOfCode inputArity (Nat.unpair code).1
              circuitBound
              coordinate }
          by_cases hcanonical : candidate.code = code
          · have hrequest : candidate = request := by
              simpa [decodeBoundedOracleRecoveryRequest, hbound,
                hcoordinate, candidate, hcanonical] using hdecode
            rw [← hrequest]
            exact hcanonical
          · simp [decodeBoundedOracleRecoveryRequest, hbound,
              hcoordinate, candidate, hcanonical] at hdecode

theorem BoundedOracleRecoveryRequest.inputArity_of_decode
    {inputArity code : ℕ} {request : BoundedOracleRecoveryRequest}
    (hdecode :
      decodeBoundedOracleRecoveryRequest inputArity code = some request) :
    request.inputArity = inputArity := by
  generalize hbound :
    decodeUnary (Nat.unpair (Nat.unpair code).2).1 = boundOption at hdecode
  cases boundOption with
  | none =>
      simp [decodeBoundedOracleRecoveryRequest, hbound] at hdecode
  | some circuitBound =>
      generalize hcoordinate :
        decodeUnary (Nat.unpair (Nat.unpair code).2).2 =
          coordinateOption at hdecode
      cases coordinateOption with
      | none =>
          simp [decodeBoundedOracleRecoveryRequest, hbound,
            hcoordinate] at hdecode
      | some coordinate =>
          let candidate : BoundedOracleRecoveryRequest :=
            { inputArity
              input :=
                requestInputOfCode inputArity (Nat.unpair code).1
              circuitBound
              coordinate }
          by_cases hcanonical : candidate.code = code
          · have hrequest : candidate = request := by
              simpa [decodeBoundedOracleRecoveryRequest, hbound,
                hcoordinate, candidate, hcanonical] using hdecode
            rw [← hrequest]
          · simp [decodeBoundedOracleRecoveryRequest, hbound,
              hcoordinate, candidate, hcanonical] at hdecode

/-! ## Fixed request-normalization prefix -/

/-- Internal handoff syntax.  The coordinate cursor is extended by one cell
because `prefixSATProgram` returns the most recently recovered prefix bit. -/
def boundedOracleRecoveryNormalizedCode
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  Nat.pair (encodeBitInput request.input) <|
    Nat.pair (encodeUnary request.circuitBound)
      (encodeUnary (request.coordinate + 1))

/-- Fixed, oracle-free normalization of the public request.

Register ABI after the halt:
* `r0`: normalized body;
* `r1`: input arity (preserved);
* `r2`: input code;
* `r4`: unary circuit bound;
* `r5`: unary `(coordinate + 1)`.
-/
def boundedOracleRecoveryRequestProgram : NPOracleProgram :=
  [ .unpairLeft 0 2 1
  , .unpairRight 0 3 2
  , .unpairLeft 3 4 3
  , .unpairRight 3 5 4
  , .set 6 1 5
  , .pair 6 5 5 6
  , .pair 4 5 3 7
  , .pair 2 3 0 8
  , .halt 0
  ]

@[simp] theorem boundedOracleRecoveryRequestProgram_length :
    boundedOracleRecoveryRequestProgram.length = 9 := by
  rfl

theorem boundedOracleRecoveryRequestProgram_oracleFree :
    OracleFree boundedOracleRecoveryRequestProgram := by
  rfl

def boundedOracleRecoveryRequestMaximumBits
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  natBitLength <|
    max request.code (boundedOracleRecoveryNormalizedCode request)

private theorem requestCode_le_requestMaximum
    (request : BoundedOracleRecoveryRequest) :
    request.code ≤
      max request.code (boundedOracleRecoveryNormalizedCode request) :=
  Nat.le_max_left _ _

private theorem normalizedCode_le_requestMaximum
    (request : BoundedOracleRecoveryRequest) :
    boundedOracleRecoveryNormalizedCode request ≤
      max request.code (boundedOracleRecoveryNormalizedCode request) :=
  Nat.le_max_right _ _

private theorem natBitLength_le_requestMaximum
    (request : BoundedOracleRecoveryRequest) {value : ℕ}
    (hvalue :
      value ≤
        max request.code (boundedOracleRecoveryNormalizedCode request)) :
    natBitLength value ≤
      boundedOracleRecoveryRequestMaximumBits request := by
  exact PolynomialClock.natBitLength_mono hvalue

private theorem requestInputCode_le_normalized
    (request : BoundedOracleRecoveryRequest) :
    encodeBitInput request.input ≤
      boundedOracleRecoveryNormalizedCode request := by
  unfold boundedOracleRecoveryNormalizedCode
  exact Nat.left_le_pair _ _

private theorem requestBoundCode_le_normalized
    (request : BoundedOracleRecoveryRequest) :
    encodeUnary request.circuitBound ≤
      boundedOracleRecoveryNormalizedCode request := by
  unfold boundedOracleRecoveryNormalizedCode
  exact
    (Nat.left_le_pair
      (encodeUnary request.circuitBound)
      (encodeUnary (request.coordinate + 1))).trans
      (Nat.right_le_pair _ _)

private theorem requestCountCode_le_normalized
    (request : BoundedOracleRecoveryRequest) :
    encodeUnary (request.coordinate + 1) ≤
      boundedOracleRecoveryNormalizedCode request := by
  unfold boundedOracleRecoveryNormalizedCode
  exact
    (Nat.right_le_pair
      (encodeUnary request.circuitBound)
      (encodeUnary (request.coordinate + 1))).trans
      (Nat.right_le_pair _ _)

private theorem requestFieldsCode_le_normalized
    (request : BoundedOracleRecoveryRequest) :
    Nat.pair (encodeUnary request.circuitBound)
        (encodeUnary (request.coordinate + 1)) ≤
      boundedOracleRecoveryNormalizedCode request := by
  unfold boundedOracleRecoveryNormalizedCode
  exact Nat.right_le_pair _ _

private theorem requestOne_le_normalized
    (request : BoundedOracleRecoveryRequest) :
    1 ≤ boundedOracleRecoveryNormalizedCode request := by
  have hcount :
      1 ≤ encodeUnary (request.coordinate + 1) := by
    rw [encodeUnary]
    exact Nat.left_le_pair 1 (encodeUnary request.coordinate)
  exact hcount.trans (requestCountCode_le_normalized request)

/-- Exact instruction trace for the public preprocessing stage.  This theorem
also records every intermediate register-width obligation; later linking
cannot silently assume that parsing or the coordinate increment was free. -/
theorem run_boundedOracleRecoveryRequestProgram
    (request : BoundedOracleRecoveryRequest) :
    runNPOracleProgram boundedOracleRecoveryRequestProgram
        (boundedOracleRecoveryRequestMaximumBits request) 9
        (initialNPOracleState request.inputArity request.code) =
      some (boundedOracleRecoveryNormalizedCode request) := by
  have hnormalizedBits :=
    natBitLength_le_requestMaximum request
      (normalizedCode_le_requestMaximum request)
  have hinputBits :=
    natBitLength_le_requestMaximum request <|
      (requestInputCode_le_normalized request).trans <|
        normalizedCode_le_requestMaximum request
  have hpublicFieldsBits :
      natBitLength
          (Nat.pair (encodeUnary request.circuitBound)
            (encodeUnary request.coordinate)) ≤
        boundedOracleRecoveryRequestMaximumBits request := by
    apply natBitLength_le_requestMaximum request
    exact
      (Nat.right_le_pair (encodeBitInput request.input)
        (Nat.pair (encodeUnary request.circuitBound)
          (encodeUnary request.coordinate))).trans
        (requestCode_le_requestMaximum request)
  have hboundBits :=
    natBitLength_le_requestMaximum request <|
      (requestBoundCode_le_normalized request).trans <|
        normalizedCode_le_requestMaximum request
  have hcoordinateBits :
      natBitLength (encodeUnary request.coordinate) ≤
        boundedOracleRecoveryRequestMaximumBits request := by
    apply natBitLength_le_requestMaximum request
    exact
      (Nat.right_le_pair 1 (encodeUnary request.coordinate)).trans <|
        (requestCountCode_le_normalized request).trans <|
          normalizedCode_le_requestMaximum request
  have honeBits :=
    natBitLength_le_requestMaximum request <|
      (requestOne_le_normalized request).trans <|
        normalizedCode_le_requestMaximum request
  have hcountBits :=
    natBitLength_le_requestMaximum request <|
      (requestCountCode_le_normalized request).trans <|
        normalizedCode_le_requestMaximum request
  have hfieldsBits :=
    natBitLength_le_requestMaximum request <|
      (requestFieldsCode_le_normalized request).trans <|
        normalizedCode_le_requestMaximum request
  have hcoordinateSucc :
      Nat.pair 1 (encodeUnary request.coordinate) =
        encodeUnary (request.coordinate + 1) := by
    rw [show request.coordinate + 1 = Nat.succ request.coordinate by
      omega]
    rfl
  have hnormalizedCodeBits :
      natBitLength
          (Nat.pair (encodeBitInput request.input)
            (Nat.pair (encodeUnary request.circuitBound)
              (encodeUnary (request.coordinate + 1)))) ≤
        boundedOracleRecoveryRequestMaximumBits request := by
    simpa only [boundedOracleRecoveryNormalizedCode] using
      hnormalizedBits
  simp [boundedOracleRecoveryRequestProgram, runNPOracleProgram,
    BoundedOracleRecoveryRequest.code,
    boundedOracleRecoveryNormalizedCode, initialNPOracleState,
    NPOracleState.boundedWrite, hpublicFieldsBits, hinputBits,
    hboundBits, hcoordinateBits, honeBits, hcoordinateSucc, hcountBits,
    hfieldsBits, hnormalizedCodeBits]

/-! ## Shared resource widening -/

private theorem boundedWrite_mono
    {state nextState : NPOracleState}
    {smallBits largeBits register value : ℕ}
    (hbits : smallBits ≤ largeBits)
    (hwrite :
      state.boundedWrite smallBits register value = some nextState) :
    state.boundedWrite largeBits register value = some nextState :=
  VerifiedLinker.boundedWrite_bits_mono hwrite hbits

/-- Successful executions are stable when the register-width envelope is
widened.  This is the resource analogue of `run_fuel_add`; linked stages can
therefore share one maximum without reproving their instruction traces. -/
theorem runNPOracleProgram_maximumBits_mono
    {program : NPOracleProgram} {smallBits largeBits fuel : ℕ}
    {state : NPOracleState} {output : ℕ}
    (hbits : smallBits ≤ largeBits)
    (hrun :
      runNPOracleProgram program smallBits fuel state = some output) :
    runNPOracleProgram program largeBits fuel state = some output := by
  induction fuel generalizing state with
  | zero =>
      simp [runNPOracleProgram] at hrun
  | succ fuel ih =>
      cases hlookup : program[state.pc]? with
      | none =>
          simp [runNPOracleProgram, hlookup] at hrun
      | some instruction =>
          cases instruction with
          | halt outputRegister =>
              by_cases hsmall :
                  natBitLength (state.registers outputRegister) ≤ smallBits
              · have hlarge := hsmall.trans hbits
                simp only [runNPOracleProgram, hlookup] at hrun ⊢
                rw [if_pos hsmall] at hrun
                rw [if_pos hlarge]
                exact hrun
              · simp only [runNPOracleProgram, hlookup] at hrun
                rw [if_neg hsmall] at hrun
                contradiction
          | set register value next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits register value with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | copy source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (state.registers source) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | increment register next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits register
                    (state.registers register + 1) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | decrement register next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              rw [Nat.pred_eq_sub_one] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits register
                    (state.registers register - 1) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | add left right destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (state.registers left + state.registers right) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | subtract left right destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (state.registers left - state.registers right) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | pair left right destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.pair (state.registers left)
                      (state.registers right)) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | unpairLeft source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.unpair (state.registers source)).1 with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | unpairRight source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.unpair (state.registers source)).2 with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | branchZero register zeroTarget nonzeroTarget =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              exact ih hrun
          | encodeNat source destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (encodeNat (state.registers source)) with
              | none =>
                  simp [hwrite] at hrun
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  exact ih (by simpa [hwrite] using hrun)
          | shiftRight source amount destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.shiftRight (state.registers source) amount) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  rw [hwrite] at hrun
                  exact ih hrun
          | shiftLeft source amount destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (Nat.shiftLeft (state.registers source) amount) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  rw [hwrite] at hrun
                  exact ih hrun
          | testBit source index destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              cases hwrite :
                  state.boundedWrite smallBits destination
                    (((state.registers source).testBit
                      (state.registers index)).toNat) with
              | none =>
                  rw [hwrite] at hrun
                  contradiction
              | some nextState =>
                  rw [boundedWrite_mono hbits hwrite]
                  rw [hwrite] at hrun
                  exact ih hrun
          | sat queryRegister destination next =>
              simp only [runNPOracleProgram, hlookup] at hrun ⊢
              by_cases hquery :
                  natBitLength (state.registers queryRegister) ≤ smallBits
              · rw [if_pos (hquery.trans hbits)]
                rw [if_pos hquery] at hrun
                cases hwrite :
                    state.boundedWrite smallBits destination
                      (encodedSat
                        (state.registers queryRegister)).toNat with
                | none =>
                    simp [hwrite] at hrun
                | some nextState =>
                    rw [boundedWrite_mono hbits hwrite]
                    exact ih (by simpa [hwrite] using hrun)
              · rw [if_neg hquery] at hrun
                contradiction

/-! ## CNF stream to zero-first input -/

/-- The canonical clause-list builder embedded between a two-instruction
header decoder and a two-instruction prefix-SAT handoff.  The coordinate
cursor lives in `r12`, outside the embedded builder's register span; it is
therefore preserved without a second copy of the list-building loop. -/
def cnfPrefixInputBuilderProgram : NPOracleProgram :=
  ([ .unpairRight 0 12 1
   , .unpairLeft 0 0 2
   ] ++
    cnfListBuilderProgram.map (continueInstruction 2 2 9)) ++
  [ .pair 2 12 0 10
  , .halt 0
  ]

@[simp] theorem cnfPrefixInputBuilderProgram_length :
    cnfPrefixInputBuilderProgram.length = 11 := by
  rfl

theorem cnfPrefixInputBuilder_oracleFree :
    OracleFree cnfPrefixInputBuilderProgram := by
  rfl

private def cnfPrefixBuilderLayout : LinkLayout where
  firstSpan := 5
  secondSpan := 0
  firstBase := 2
  resetBase := 9
  secondBase := 9
  secondRegisterBase := 5
  savedLengthRegister := 12
  transferRegister := 2

private theorem cnfPrefixInputBuilder_continued :
    ProgramContinuedAt cnfPrefixInputBuilderProgram cnfListBuilderProgram
      cnfPrefixBuilderLayout.firstBase
      cnfPrefixBuilderLayout.transferRegister
      cnfPrefixBuilderLayout.resetBase := by
  intro pc instruction hlookup
  have hpc : pc < cnfListBuilderProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [cnfPrefixBuilderLayout] at *
  have hpc' : pc < 7 := by
    simpa [cnfListBuilderProgram] using hpc
  interval_cases pc <;>
    simp [cnfListBuilderProgram] at hlookup
  all_goals subst instruction
  all_goals rfl

private theorem cnfListBuilderProgram_span :
    programRegisterSpan cnfListBuilderProgram ≤
      cnfPrefixBuilderLayout.firstSpan := by
  rfl

def cnfPrefixInputBuilderFuel (formula : EncodedCNF) : ℕ :=
  cnfListBuilderFuel ((formula.map Encodable.encode).reverse) + 4

private theorem npOracleState_ext
    (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem cnfPrefixBuilder_entry
    (inputLength : ℕ) (formula : EncodedCNF) (countCode : ℕ) :
    let stream :=
      encodeTaggedList ((formula.map Encodable.encode).reverse)
    let publicState :=
      initialNPOracleState inputLength
        (Nat.pair stream countCode)
    let parsed :=
      (((publicState.write 12 countCode).jump 1).write 0 stream).jump 2
    let sourceState :=
      initialNPOracleState inputLength stream
    parsed =
      firstStageState cnfPrefixBuilderLayout countCode sourceState := by
  dsimp only
  apply npOracleState_ext
  · rfl
  · funext register
    by_cases hzero : register = 0
    · subst register
      simp [initialNPOracleState, firstStageState,
        cnfPrefixBuilderLayout, NPOracleState.write,
        NPOracleState.jump]
    · by_cases hone : register = 1
      · subst register
        simp [initialNPOracleState, firstStageState,
          cnfPrefixBuilderLayout, NPOracleState.write,
          NPOracleState.jump]
      · by_cases hcount : register = 12
        · subst register
          simp [initialNPOracleState, firstStageState,
            cnfPrefixBuilderLayout, NPOracleState.write,
            NPOracleState.jump]
        · by_cases hlow : register < 5
          · interval_cases register <;>
              simp_all [initialNPOracleState, firstStageState,
                cnfPrefixBuilderLayout, NPOracleState.write,
                NPOracleState.jump]
          · simp [initialNPOracleState, firstStageState,
              cnfPrefixBuilderLayout, NPOracleState.write,
              NPOracleState.jump, hzero, hone, hcount, hlow]

/-- A structural reverse stream is converted to exactly the public input of
`prefixSATProgram`.  The proof reuses `run_cnfListBuilder` through the verified
continued-program simulation, so there is one clause-list implementation. -/
theorem run_cnfPrefixInputBuilderProgram
    (inputLength count : ℕ) (formula : EncodedCNF)
    {maximumBits sourceBound formulaBound prefixBound : ℕ}
    (hsource :
      encodeTaggedList
          ((formula.map Encodable.encode).reverse) ≤ sourceBound)
    (hformula : Encodable.encode formula ≤ formulaBound)
    (hprefix : prefixSATInput count formula ≤ prefixBound)
    (hbits :
      natBitLength
          (max sourceBound (max formulaBound prefixBound)) ≤
        maximumBits) :
    runNPOracleProgram cnfPrefixInputBuilderProgram maximumBits
        (cnfPrefixInputBuilderFuel formula)
        (initialNPOracleState inputLength
          (Nat.pair
            (encodeTaggedList
              ((formula.map Encodable.encode).reverse))
            (encodeUnary count))) =
      some (prefixSATInput count formula) := by
  let stream :=
    encodeTaggedList ((formula.map Encodable.encode).reverse)
  let sourceState :=
    initialNPOracleState inputLength stream
  have hsourceFormulaBits :
      natBitLength (max sourceBound formulaBound) ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact max_le
      (Nat.le_max_left _ _)
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hrunBuilder :
      runNPOracleProgram cnfListBuilderProgram maximumBits
          (cnfListBuilderFuel
            ((formula.map Encodable.encode).reverse))
          sourceState =
        some (Encodable.encode formula) := by
    have run := run_cnfListBuilder_from
      ((formula.map Encodable.encode).reverse) []
      (sourceBound := sourceBound) (outputBound := formulaBound)
      sourceState
      (by rfl)
      (by simp [sourceState, stream, initialNPOracleState])
      (by simp [sourceState, initialNPOracleState, encodeCodeList])
      hsource
      (by simpa [encodeCodeList_map_encode] using hformula)
      hsourceFormulaBits
    simpa [encodeCodeList_map_encode] using run
  have hcountBits :
      natBitLength (encodeUnary count) ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact
      ((Nat.right_le_pair (Encodable.encode formula)
        (encodeUnary count)).trans hprefix).trans
        ((Nat.le_max_right formulaBound prefixBound).trans
          (Nat.le_max_right sourceBound
            (max formulaBound prefixBound)))
  have hstreamBits : natBitLength stream ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact hsource.trans (Nat.le_max_left _ _)
  rw [show cnfPrefixInputBuilderFuel formula =
      (cnfListBuilderFuel
        ((formula.map Encodable.encode).reverse) + 2) + 2 by
      simp [cnfPrefixInputBuilderFuel]]
  rw [run_unpairRight_instruction
    (program := cnfPrefixInputBuilderProgram)
    (fuel :=
      cnfListBuilderFuel ((formula.map Encodable.encode).reverse) + 3)
    (by rfl) rfl (by
      simp [initialNPOracleState]) hcountBits]
  let state1 :=
    ((initialNPOracleState inputLength
      (Nat.pair stream (encodeUnary count))).write
        12 (encodeUnary count)).jump 1
  rw [show
      cnfListBuilderFuel ((formula.map Encodable.encode).reverse) + 3 =
        (cnfListBuilderFuel
          ((formula.map Encodable.encode).reverse) + 2) + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := cnfPrefixInputBuilderProgram)
    (fuel :=
      cnfListBuilderFuel ((formula.map Encodable.encode).reverse) + 2)
    (by rfl) rfl (by
      simp [stream, initialNPOracleState, NPOracleState.write,
        NPOracleState.jump]) hstreamBits]
  let parsed := (state1.write 0 stream).jump 2
  have hentry :
      parsed =
        firstStageState cnfPrefixBuilderLayout (encodeUnary count)
          sourceState := by
    exact cnfPrefixBuilder_entry inputLength formula (encodeUnary count)
  change
    runNPOracleProgram cnfPrefixInputBuilderProgram maximumBits
        (cnfListBuilderFuel
          ((formula.map Encodable.encode).reverse) + 2) parsed =
      some (prefixSATInput count formula)
  rw [hentry]
  apply run_continued
    cnfPrefixInputBuilder_continued
    cnfListBuilderProgram_span hrunBuilder
  intro haltState unused
  have hprefixBits :
      natBitLength (prefixSATInput count formula) ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact hprefix.trans <|
      (Nat.le_max_right formulaBound prefixBound).trans
        (Nat.le_max_right sourceBound (max formulaBound prefixBound))
  have hpairAt :
      cnfPrefixInputBuilderProgram[9]? =
        some (.pair 2 12 0 10) := by
    rfl
  have hhaltAt :
      cnfPrefixInputBuilderProgram[10]? =
        some (.halt 0) := by
    rfl
  rw [show unused + 2 = (unused + 1) + 1 by omega]
  rw [run_pair_instruction
    (fuel := unused + 1) hpairAt rfl
    (by
      simp [firstStageState, cnfPrefixBuilderLayout,
        NPOracleState.write, NPOracleState.jump, prefixSATInput])
    hprefixBits]
  let finishState :=
    (((((firstStageState cnfPrefixBuilderLayout (encodeUnary count)
        haltState).write cnfPrefixBuilderLayout.transferRegister
          (Encodable.encode formula)).jump
        cnfPrefixBuilderLayout.resetBase).write
      0 (prefixSATInput count formula)).jump 10)
  change
    runNPOracleProgram cnfPrefixInputBuilderProgram maximumBits
        (unused + 1) finishState =
      some (prefixSATInput count formula)
  have hhalt :
      runNPOracleProgram cnfPrefixInputBuilderProgram maximumBits
          1 finishState =
        some (prefixSATInput count formula) := by
    apply run_halt_instruction hhaltAt rfl
    · simp [finishState, NPOracleState.write, NPOracleState.jump]
    · simpa [finishState, NPOracleState.write, NPOracleState.jump] using
        hprefixBits
  have hwiden := run_fuel_add hhalt unused
  simpa only [Nat.add_comm] using hwiden

def cnfPrefixStreamInput (count : ℕ) (formula : EncodedCNF) : ℕ :=
  Nat.pair
    (encodeTaggedList ((formula.map Encodable.encode).reverse))
    (encodeUnary count)

def cnfPrefixInputBuilderMaximumBits
    (count : ℕ) (formula : EncodedCNF) : ℕ :=
  natBitLength <|
    max
      (encodeTaggedList ((formula.map Encodable.encode).reverse))
      (max (Encodable.encode formula) (prefixSATInput count formula))

/-! ## Forward raw triples to the canonical prefix-SAT input -/

/-- A two-instruction decoder, the one shared structural-clause encoder, and
a two-instruction handoff.  The coordinate cursor is isolated in `r20`, above
the encoder's complete register span. -/
def structuralClausePrefixBuilderProgram : NPOracleProgram :=
  ([ .unpairRight 0 20 1
   , .unpairLeft 0 0 2
   ] ++
    structuralClauseStreamProgram.map
      (continueInstruction 2 2 22)) ++
  [ .pair 2 20 0 23
  , .halt 0
  ]

@[simp] theorem structuralClausePrefixBuilderProgram_length :
    structuralClausePrefixBuilderProgram.length = 24 := by
  rfl

theorem structuralClausePrefixBuilderProgram_oracleFree :
    OracleFree structuralClausePrefixBuilderProgram := by
  rfl

private def structuralClausePrefixLayout : LinkLayout where
  firstSpan := 14
  secondSpan := 0
  firstBase := 2
  resetBase := 22
  secondBase := 22
  secondRegisterBase := 14
  savedLengthRegister := 20
  transferRegister := 2

private theorem structuralClausePrefix_continued :
    ProgramContinuedAt structuralClausePrefixBuilderProgram
      structuralClauseStreamProgram
      structuralClausePrefixLayout.firstBase
      structuralClausePrefixLayout.transferRegister
      structuralClausePrefixLayout.resetBase := by
  intro pc instruction hlookup
  have hpc : pc < structuralClauseStreamProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralClausePrefixLayout] at *
  have hpc' : pc < 20 := by
    simpa [structuralClauseStreamProgram] using hpc
  interval_cases pc <;>
    simp [structuralClauseStreamProgram] at hlookup
  all_goals subst instruction
  all_goals rfl

private theorem structuralClauseStreamProgram_span :
    programRegisterSpan structuralClauseStreamProgram ≤
      structuralClausePrefixLayout.firstSpan := by
  rfl

def structuralClausePrefixBuilderFuel (formula : EncodedCNF) : ℕ :=
  structuralClauseStreamFuel formula + 4

private theorem structuralClausePrefix_entry
    (inputLength count : ℕ) (formula : EncodedCNF) :
    let rawStream := rawClauseStream formula
    let publicState :=
      initialNPOracleState inputLength
        (Nat.pair rawStream (encodeUnary count))
    let parsed :=
      (((publicState.write 20 (encodeUnary count)).jump 1).write
        0 rawStream).jump 2
    let sourceState :=
      initialNPOracleState inputLength rawStream
    parsed =
      firstStageState structuralClausePrefixLayout (encodeUnary count)
        sourceState := by
  dsimp only
  apply npOracleState_ext
  · rfl
  · funext register
    by_cases hzero : register = 0
    · subst register
      simp [initialNPOracleState, firstStageState,
        structuralClausePrefixLayout, NPOracleState.write,
        NPOracleState.jump]
    · by_cases hone : register = 1
      · subst register
        simp [initialNPOracleState, firstStageState,
          structuralClausePrefixLayout, NPOracleState.write,
          NPOracleState.jump]
      · by_cases hcount : register = 20
        · subst register
          simp [initialNPOracleState, firstStageState,
            structuralClausePrefixLayout, NPOracleState.write,
            NPOracleState.jump]
        · by_cases hlow : register < 14
          · interval_cases register <;>
              simp_all [initialNPOracleState, firstStageState,
                structuralClausePrefixLayout, NPOracleState.write,
                NPOracleState.jump]
          · simp [initialNPOracleState, firstStageState,
              structuralClausePrefixLayout, NPOracleState.write,
              NPOracleState.jump, hzero, hone, hcount, hlow]

/-- Exact fixed-program conversion from forward structural literal triples to
the public input of `cnfPrefixSATProgram`. -/
theorem run_structuralClausePrefixBuilderProgram
    (inputLength count : ℕ) (formula : EncodedCNF)
    (hthree :
      formula.all (fun clause => clause.length = 3) = true)
    {maximumBits sourceBound streamBound prefixBound : ℕ}
    (hsource : rawClauseStream formula ≤ sourceBound)
    (hstream :
      canonicalReverseClauseStream formula ≤ streamBound)
    (hprefix : cnfPrefixStreamInput count formula ≤ prefixBound)
    (hbits :
      natBitLength
          (max sourceBound (max streamBound prefixBound)) ≤
        maximumBits) :
    runNPOracleProgram structuralClausePrefixBuilderProgram maximumBits
        (structuralClausePrefixBuilderFuel formula)
        (initialNPOracleState inputLength
          (Nat.pair (rawClauseStream formula) (encodeUnary count))) =
      some (cnfPrefixStreamInput count formula) := by
  let rawStream := rawClauseStream formula
  let canonicalStream := canonicalReverseClauseStream formula
  let sourceState := initialNPOracleState inputLength rawStream
  have hencoderBits :
      structuralClauseStreamMaximumBits formula ≤ maximumBits := by
    unfold structuralClauseStreamMaximumBits
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact max_le
      (hsource.trans (Nat.le_max_left _ _))
      (hstream.trans <|
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hrunEncoder :
      runNPOracleProgram structuralClauseStreamProgram maximumBits
          (structuralClauseStreamFuel formula) sourceState =
        some canonicalStream := by
    apply runNPOracleProgram_maximumBits_mono hencoderBits
    exact run_structuralClauseStreamProgram formula hthree inputLength
  have hcountBits :
      natBitLength (encodeUnary count) ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact
      ((Nat.right_le_pair canonicalStream (encodeUnary count)).trans <|
        by simpa only [cnfPrefixStreamInput, canonicalStream,
          canonicalReverseClauseStream] using hprefix).trans <|
        (Nat.le_max_right streamBound prefixBound).trans
          (Nat.le_max_right sourceBound (max streamBound prefixBound))
  have hrawBits : natBitLength rawStream ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact hsource.trans (Nat.le_max_left _ _)
  rw [show structuralClausePrefixBuilderFuel formula =
      (structuralClauseStreamFuel formula + 2) + 2 by
      simp [structuralClausePrefixBuilderFuel]]
  rw [run_unpairRight_instruction
    (program := structuralClausePrefixBuilderProgram)
    (fuel := structuralClauseStreamFuel formula + 3)
    (by rfl) rfl (by simp [initialNPOracleState]) hcountBits]
  let state1 :=
    ((initialNPOracleState inputLength
      (Nat.pair rawStream (encodeUnary count))).write
        20 (encodeUnary count)).jump 1
  rw [show structuralClauseStreamFuel formula + 3 =
      (structuralClauseStreamFuel formula + 2) + 1 by omega]
  rw [run_unpairLeft_instruction
    (program := structuralClausePrefixBuilderProgram)
    (fuel := structuralClauseStreamFuel formula + 2)
    (by rfl) rfl
    (by simp [rawStream, initialNPOracleState,
      NPOracleState.write, NPOracleState.jump])
    hrawBits]
  let parsed := (state1.write 0 rawStream).jump 2
  have hentry :
      parsed =
        firstStageState structuralClausePrefixLayout (encodeUnary count)
          sourceState :=
    structuralClausePrefix_entry inputLength count formula
  change
    runNPOracleProgram structuralClausePrefixBuilderProgram maximumBits
        (structuralClauseStreamFuel formula + 2) parsed =
      some (cnfPrefixStreamInput count formula)
  rw [hentry]
  apply run_continued
    structuralClausePrefix_continued
    structuralClauseStreamProgram_span hrunEncoder
  intro haltState unused
  have hprefixBits :
      natBitLength (cnfPrefixStreamInput count formula) ≤ maximumBits := by
    apply (PolynomialClock.natBitLength_mono ?_).trans hbits
    exact hprefix.trans <|
      (Nat.le_max_right streamBound prefixBound).trans
        (Nat.le_max_right sourceBound (max streamBound prefixBound))
  rw [show unused + 2 = (unused + 1) + 1 by omega]
  rw [run_pair_instruction
    (program := structuralClausePrefixBuilderProgram)
    (pc := 22) (left := 2) (right := 20) (destination := 0)
    (next := 23) (value := cnfPrefixStreamInput count formula)
    (by rfl) rfl
    (by
      simp [firstStageState, structuralClausePrefixLayout,
        NPOracleState.write, NPOracleState.jump, cnfPrefixStreamInput,
        canonicalStream, canonicalReverseClauseStream])
    hprefixBits]
  let finishState :=
    (((((firstStageState structuralClausePrefixLayout (encodeUnary count)
        haltState).write structuralClausePrefixLayout.transferRegister
          canonicalStream).jump
        structuralClausePrefixLayout.resetBase).write
      0 (cnfPrefixStreamInput count formula)).jump 23)
  change
    runNPOracleProgram structuralClausePrefixBuilderProgram maximumBits
        (unused + 1) finishState =
      some (cnfPrefixStreamInput count formula)
  have hhalt :
      runNPOracleProgram structuralClausePrefixBuilderProgram maximumBits
          1 finishState =
        some (cnfPrefixStreamInput count formula) := by
    apply run_halt_instruction (pc := 23) (by rfl) rfl
    · simp [finishState, NPOracleState.write, NPOracleState.jump]
    · simpa [finishState, NPOracleState.write, NPOracleState.jump] using
        hprefixBits
  have hwiden := run_fuel_add hhalt unused
  simpa only [Nat.add_comm] using hwiden

/-- One fixed composition from structural reverse-clause syntax to the
zero-first SAT self-reducer.  The only SAT instructions are those already
owned by `prefixSATProgram`. -/
def cnfPrefixSATProgram : NPOracleProgram :=
  linkPrograms cnfPrefixInputBuilderProgram prefixSATProgram

def cnfPrefixSATFuel (count : ℕ) (formula : EncodedCNF) : ℕ :=
  linkFuel prefixSATProgram
    (cnfPrefixInputBuilderFuel formula)
    (prefixSATFuel count formula)

def cnfPrefixSATMaximumBits
    (inputLength count : ℕ) (formula : EncodedCNF) : ℕ :=
  max (natBitLength inputLength) <|
    max (cnfPrefixInputBuilderMaximumBits count formula)
      (prefixSATMaximumBits count formula)

theorem cnfPrefixSATProgram_containsSAT :
    containsSAT cnfPrefixSATProgram = true := by
  change
    containsSAT
        (linkPrograms cnfPrefixInputBuilderProgram prefixSATProgram) =
      true
  rw [containsSAT_linkPrograms]
  simp [prefixSATProgram, containsSAT]

/-- Exact executable recovery from a generated clause stream.  No formula
code appears in the machine input: the first linked stage constructs it from
the reverse clause stream, and the second stage performs the canonical
zero-first oracle search. -/
theorem run_cnfPrefixSATProgram
    (inputLength count : ℕ) (formula : EncodedCNF) :
    runNPOracleProgram cnfPrefixSATProgram
        (cnfPrefixSATMaximumBits inputLength count formula)
        (cnfPrefixSATFuel count formula)
        (initialNPOracleState inputLength
          (cnfPrefixStreamInput count formula)) =
      some (prefixSATOutput count formula) := by
  have hbuilderBits :
      cnfPrefixInputBuilderMaximumBits count formula ≤
        cnfPrefixSATMaximumBits inputLength count formula := by
    unfold cnfPrefixSATMaximumBits
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hprefixBits :
      prefixSATMaximumBits count formula ≤
        cnfPrefixSATMaximumBits inputLength count formula := by
    unfold cnfPrefixSATMaximumBits
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlengthBits :
      natBitLength inputLength ≤
        cnfPrefixSATMaximumBits inputLength count formula := by
    exact Nat.le_max_left _ _
  have hpositive :
      1 ≤ cnfPrefixSATMaximumBits inputLength count formula := by
    have hprefixPositive :
        1 ≤ prefixSATMaximumBits count formula := by
      unfold prefixSATMaximumBits natBitLength
      omega
    exact hprefixPositive.trans hprefixBits
  apply run_linkPrograms hpositive hlengthBits
  · apply run_cnfPrefixInputBuilderProgram inputLength count formula
      (sourceBound :=
        encodeTaggedList ((formula.map Encodable.encode).reverse))
      (formulaBound := Encodable.encode formula)
      (prefixBound := prefixSATInput count formula)
    · rfl
    · rfl
    · rfl
    · simpa only [cnfPrefixInputBuilderMaximumBits] using hbuilderBits
  · apply runNPOracleProgram_maximumBits_mono hprefixBits
    exact run_prefixSATProgram count inputLength formula

/-- Complete fixed suffix from forward raw Tseitin triples to the recovered
prefix bit.  Canonical clause encoding, reversal, CNF construction, and SAT
self-reduction are all interpreter traces. -/
def rawClausePrefixSATProgram : NPOracleProgram :=
  linkPrograms structuralClausePrefixBuilderProgram cnfPrefixSATProgram

def rawClausePrefixSATFuel (count : ℕ) (formula : EncodedCNF) : ℕ :=
  linkFuel cnfPrefixSATProgram
    (structuralClausePrefixBuilderFuel formula)
    (cnfPrefixSATFuel count formula)

def structuralClausePrefixBuilderMaximumBits
    (count : ℕ) (formula : EncodedCNF) : ℕ :=
  natBitLength <|
    max (rawClauseStream formula) <|
      max (canonicalReverseClauseStream formula)
        (cnfPrefixStreamInput count formula)

def rawClausePrefixSATMaximumBits
    (inputLength count : ℕ) (formula : EncodedCNF) : ℕ :=
  max (natBitLength inputLength) <|
    max (structuralClausePrefixBuilderMaximumBits count formula)
      (cnfPrefixSATMaximumBits inputLength count formula)

theorem rawClausePrefixSATProgram_containsSAT :
    containsSAT rawClausePrefixSATProgram = true := by
  rw [rawClausePrefixSATProgram, containsSAT_linkPrograms,
    cnfPrefixSATProgram_containsSAT]
  simp [containsSAT]

theorem run_rawClausePrefixSATProgram
    (inputLength count : ℕ) (formula : EncodedCNF)
    (hthree :
      formula.all (fun clause => clause.length = 3) = true) :
    runNPOracleProgram rawClausePrefixSATProgram
        (rawClausePrefixSATMaximumBits inputLength count formula)
        (rawClausePrefixSATFuel count formula)
        (initialNPOracleState inputLength
          (Nat.pair (rawClauseStream formula) (encodeUnary count))) =
      some (prefixSATOutput count formula) := by
  have hbuilderBits :
      structuralClausePrefixBuilderMaximumBits count formula ≤
        rawClausePrefixSATMaximumBits inputLength count formula := by
    unfold rawClausePrefixSATMaximumBits
    exact
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsuffixBits :
      cnfPrefixSATMaximumBits inputLength count formula ≤
        rawClausePrefixSATMaximumBits inputLength count formula := by
    unfold rawClausePrefixSATMaximumBits
    exact
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlengthBits :
      natBitLength inputLength ≤
        rawClausePrefixSATMaximumBits inputLength count formula :=
    Nat.le_max_left _ _
  have hpositive :
      1 ≤ rawClausePrefixSATMaximumBits inputLength count formula := by
    have hsuffixPositive :
        1 ≤ cnfPrefixSATMaximumBits inputLength count formula := by
      unfold cnfPrefixSATMaximumBits
      have :
          1 ≤ prefixSATMaximumBits count formula := by
        unfold prefixSATMaximumBits natBitLength
        omega
      exact this.trans <|
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact hsuffixPositive.trans hsuffixBits
  apply run_linkPrograms hpositive hlengthBits
  · apply runNPOracleProgram_maximumBits_mono hbuilderBits
    apply run_structuralClausePrefixBuilderProgram
      inputLength count formula hthree
      (sourceBound := rawClauseStream formula)
      (streamBound := canonicalReverseClauseStream formula)
      (prefixBound := cnfPrefixStreamInput count formula)
    · rfl
    · rfl
    · rfl
    · rfl
  · apply runNPOracleProgram_maximumBits_mono hsuffixBits
    exact run_cnfPrefixSATProgram inputLength count formula

/-- The exact semantic result expected from the linked runtime.  The
coordinate count is one-based at the self-reducer boundary because its output
is the latest recovered bit of a prefix. -/
def boundedOracleRecoveryOutput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  prefixSATOutput (request.coordinate + 1)
    (boundedOracleRecoveryFormula pcp.toSemantic request.input
      request.circuitBound)

def boundedOracleRecoveryStructuralInput
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  Nat.pair
    (rawClauseStream <|
      boundedOracleRecoveryFormula pcp.toSemantic request.input
        request.circuitBound)
    (encodeUnary (request.coordinate + 1))

def boundedOracleRecoveryStructuralMaximumBits
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  rawClausePrefixSATMaximumBits request.inputArity
    (request.coordinate + 1)
    (boundedOracleRecoveryFormula pcp.toSemantic request.input
      request.circuitBound)

def boundedOracleRecoveryStructuralFuel
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) : ℕ :=
  rawClausePrefixSATFuel (request.coordinate + 1)
    (boundedOracleRecoveryFormula pcp.toSemantic request.input
      request.circuitBound)

/-- Exact C.12 structural suffix theorem.  The machine input contains forward
literal triples—not a canonical formula code or an answer—and the fixed trace
performs reversal, canonical CNF construction, and zero-first SAT recovery. -/
theorem run_boundedOracleRecoveryStructuralSuffix
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) :
    runNPOracleProgram rawClausePrefixSATProgram
        (boundedOracleRecoveryStructuralMaximumBits pcp request)
        (boundedOracleRecoveryStructuralFuel pcp request)
        (initialNPOracleState request.inputArity
          (boundedOracleRecoveryStructuralInput pcp request)) =
      some (boundedOracleRecoveryOutput pcp request) := by
  apply run_rawClausePrefixSATProgram request.inputArity
    (request.coordinate + 1)
    (boundedOracleRecoveryFormula pcp.toSemantic request.input
      request.circuitBound)
  exact circuitInputFormula_threeLiteral
    (boundedOracleVerifierCircuit pcp.toSemantic request.input
      request.circuitBound)

def boundedOracleRecoveryBit
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) : Bool :=
  decide (boundedOracleRecoveryOutput pcp request ≠ 0)

@[simp] theorem boundedOracleRecoveryBit_eq
    {machine : SourceInterfaces.TimedDecisionMachine}
    {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound)
    (request : BoundedOracleRecoveryRequest) :
    boundedOracleRecoveryBit pcp request =
      decide
        (prefixSATOutput (request.coordinate + 1)
          (boundedOracleRecoveryFormula pcp.toSemantic request.input
            request.circuitBound) ≠ 0) := by
  rfl

end NearCubicWires.BoundedOracleRecoveryProgram
