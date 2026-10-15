import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Circuits.CallableRelocation

/-!
# Canonical balanced call traversal

This module gives one executable ABI for applying a verified oracle program to
a variable list of requests.  Both requests and outputs use
`encodeBalancedList`; the controller therefore has linear fuel and logarithmic
structural depth instead of materializing a linked-list integer.
-/

namespace NearCubicWires.CanonicalBalancedCall

open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

private theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right := by
  unfold natBitLength
  exact Nat.add_le_add_right (Nat.log_mono_right hle) 1

structure BalancedCallLayout where
  calleeSpan : ℕ
  leafPc : ℕ
  resetBase : ℕ
  decodeBase : ℕ
  calleeBase : ℕ
  returnPc : ℕ
  donePc : ℕ
  calleeRegisterBase : ℕ
  deriving Repr

def balancedCallLayout (callee : NPOracleProgram) : BalancedCallLayout :=
  let calleeSpan := programRegisterSpan callee
  let leafPc := 34
  let resetBase := leafPc
  let decodeBase := resetBase + calleeSpan
  let calleeBase := decodeBase + 2
  let returnPc := calleeBase + callee.length
  { calleeSpan
    leafPc
    resetBase
    decodeBase
    calleeBase
    returnPc
    donePc := returnPc + 1
    calleeRegisterBase := 9 }

/-- The leaf handler clears a private register bank, decodes
`pair(inputLength, requestCode)`, invokes the relocated callee, extracts its
raw output, and returns to the single balanced controller. -/
def balancedCallProgram (callee : NPOracleProgram) : NPOracleProgram :=
  let layout := balancedCallLayout callee
  (((balancedTraversalController layout.leafPc layout.donePc ++
      resetRegisters layout.calleeRegisterBase layout.calleeSpan
        layout.resetBase) ++
      [ .unpairLeft 3 (layout.calleeRegisterBase + 1)
          (layout.decodeBase + 1)
      , .unpairRight 3 layout.calleeRegisterBase layout.calleeBase
      ]) ++
      callee.map
        (callableInstruction layout.calleeBase layout.calleeRegisterBase
          3 layout.returnPc)) ++
      [ .unpairRight 3 3 balancedTraversalLeafReturnPc
      , .halt 0
      ]

theorem balancedCallProgram_controllerAt (callee : NPOracleProgram) :
    BalancedTraversalControllerAt (balancedCallProgram callee)
      (balancedCallLayout callee).leafPc
      (balancedCallLayout callee).donePc := by
  intro pc instruction hlookup
  have hpc :
      pc <
        (balancedTraversalController
          (balancedCallLayout callee).leafPc
          (balancedCallLayout callee).donePc).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedCallProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append]
    omega)]
  rw [List.getElem?_append_left hpc]
  exact hlookup

theorem balancedCallProgram_resetAt (callee : NPOracleProgram) :
    ResetProgramAt (balancedCallProgram callee)
      (balancedCallLayout callee).calleeRegisterBase
      (balancedCallLayout callee).calleeSpan
      (balancedCallLayout callee).resetBase := by
  intro index hindex
  change index < programRegisterSpan callee at hindex
  simp only [balancedCallProgram, balancedCallLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [balancedTraversalController_length]
    omega)]
  simp only [balancedTraversalController_length]
  rw [show 34 + index - 34 = index by omega]
  simp only [resetRegisters, List.getElem?_map]
  rw [List.getElem?_range hindex]
  rfl

theorem balancedCallProgram_decodeAt (callee : NPOracleProgram)
    (index : ℕ) (hindex : index < 2) :
    (balancedCallProgram callee)[
      (balancedCallLayout callee).decodeBase + index]? =
      ([
        .unpairLeft 3 ((balancedCallLayout callee).calleeRegisterBase + 1)
          ((balancedCallLayout callee).decodeBase + 1),
        .unpairRight 3 (balancedCallLayout callee).calleeRegisterBase
          (balancedCallLayout callee).calleeBase
      ] : NPOracleProgram)[index]? := by
  simp only [balancedCallProgram, balancedCallLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length]
  rw [show 34 + programRegisterSpan callee + index -
      (34 + programRegisterSpan callee) = index by omega]

theorem balancedCallProgram_callableAt (callee : NPOracleProgram) :
    ProgramCallableAt (balancedCallProgram callee) callee
      (balancedCallLayout callee).calleeBase
      (balancedCallLayout callee).calleeRegisterBase 3
      (balancedCallLayout callee).returnPc := by
  intro pc instruction hlookup
  have hpc : pc < callee.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [balancedCallProgram, balancedCallLayout]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length, List.length_cons, List.length_nil]
  rw [show 34 + programRegisterSpan callee + 2 + pc -
      (34 + programRegisterSpan callee + 2) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem balancedCallProgram_return (callee : NPOracleProgram) :
    (balancedCallProgram callee)[
      (balancedCallLayout callee).returnPc]? =
      some (.unpairRight 3 3 balancedTraversalLeafReturnPc) := by
  simp only [balancedCallProgram, balancedCallLayout]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length, List.length_cons, List.length_nil,
    List.length_map]
  rw [show 34 + programRegisterSpan callee + 2 + callee.length -
      (34 + programRegisterSpan callee + 2 + callee.length) = 0 by omega]
  rfl

theorem balancedCallProgram_halt (callee : NPOracleProgram) :
    (balancedCallProgram callee)[
      (balancedCallLayout callee).donePc]? =
      some (.halt 0) := by
  simp only [balancedCallProgram, balancedCallLayout]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, balancedTraversalController_length,
      resetRegisters_length, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, balancedTraversalController_length,
    resetRegisters_length, List.length_cons, List.length_nil,
    List.length_map]
  rw [show 34 + programRegisterSpan callee + 2 + callee.length + 1 -
      (34 + programRegisterSpan callee + 2 + callee.length) = 1 by omega]
  rfl

private theorem oracleFree_callableMap
    {callee : NPOracleProgram} (hcallee : OracleFree callee)
    (pcOffset registerOffset accumulatorRegister returnPc : ℕ) :
    OracleFree
      (callee.map (callableInstruction pcOffset registerOffset
        accumulatorRegister returnPc)) := by
  rw [oracleFree_iff_containsSAT_false] at hcallee ⊢
  unfold containsSAT at hcallee ⊢
  rw [List.any_map]
  change callee.any (fun instruction =>
    match callableInstruction pcOffset registerOffset accumulatorRegister
        returnPc instruction with
    | .sat _ _ _ => true
    | _ => false) = false
  exact (any_callableInstruction callee pcOffset registerOffset
    accumulatorRegister returnPc).trans hcallee

private theorem oracleFree_append
    {first second : NPOracleProgram}
    (hfirst : OracleFree first) (hsecond : OracleFree second) :
    OracleFree (first ++ second) := by
  unfold OracleFree at hfirst hsecond ⊢
  simp [hfirst, hsecond]

private theorem oracleFree_resetRegisters
    (firstRegister count startPc : ℕ) :
    OracleFree (resetRegisters firstRegister count startPc) := by
  unfold OracleFree
  simp [resetRegisters, List.all_map]

theorem balancedCallProgram_oracleFree
    {callee : NPOracleProgram} (hcallee : OracleFree callee) :
    OracleFree (balancedCallProgram callee) := by
  let layout := balancedCallLayout callee
  have hcontroller :=
    balancedTraversalController_oracleFree layout.leafPc layout.donePc
  have hcallable :=
    oracleFree_callableMap hcallee layout.calleeBase
      layout.calleeRegisterBase 3 layout.returnPc
  have hreset :=
    oracleFree_resetRegisters layout.calleeRegisterBase layout.calleeSpan
      layout.resetBase
  have hdecode : OracleFree
      [ .unpairLeft 3 (layout.calleeRegisterBase + 1)
          (layout.decodeBase + 1)
      , .unpairRight 3 layout.calleeRegisterBase layout.calleeBase
      ] := by rfl
  have htail : OracleFree
      [ .unpairRight 3 3 balancedTraversalLeafReturnPc
      , .halt 0
      ] := by rfl
  simpa [balancedCallProgram, layout] using
    oracleFree_append
      (oracleFree_append
        (oracleFree_append
          (oracleFree_append hcontroller hreset) hdecode)
        hcallable)
      htail

/-! ## Native-input request framing -/

/-- The canonical balanced-call request carries the callee's native input
length once beside its raw request code. -/
def nativeInputRequest (inputLength requestCode : ℕ) : ℕ :=
  Nat.pair inputLength requestCode

/-- Map a balanced tree of raw codes to native-input requests.  The preserved
public input length in `r1` is the only source of the request's left field. -/
def nativeInputRequestTreeProgram : NPOracleProgram :=
  balancedTraversalController 34 35 ++
    [ .pair 1 3 3 balancedTraversalLeafReturnPc
    , .halt 0
    ]

@[simp] theorem nativeInputRequestTreeProgram_oracleFree :
    OracleFree nativeInputRequestTreeProgram := by
  rfl

theorem nativeInputRequestTreeProgram_controllerAt :
    BalancedTraversalControllerAt
      nativeInputRequestTreeProgram 34 35 := by
  intro pc instruction hlookup
  have hpc : pc < (balancedTraversalController 34 35).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [nativeInputRequestTreeProgram]
  rw [List.getElem?_append_left hpc]
  exact hlookup

def nativeInputRequestTreeFuel (requestCodes : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps
      (balancedTraversalTree requestCodes) +
    requestCodes.length + 2

def nativeInputRequestTreeBits
    (inputLength : ℕ) (requestCodes : List ℕ) : ℕ :=
  max (natBitLength inputLength) <|
    balancedTraversalRequiredBits (nativeInputRequest inputLength)
      (balancedTraversalTree requestCodes) []

private theorem run_nativeInputRequestTreeLeaf
    (inputLength requestCode maximumBits : ℕ)
    (entry : NPOracleState)
    (hpc : entry.pc = 34)
    (hcurrent : entry.registers 0 = Nat.pair 1 requestCode)
    (hatom : entry.registers 3 = requestCode)
    (hbits :
      natBitLength (nativeInputRequest inputLength requestCode) ≤
        maximumBits)
    (hentryLength : entry.registers 1 = inputLength) :
    ∃ finish,
      RunsToIn nativeInputRequestTreeProgram maximumBits
          1 entry finish ∧
      finish.pc = balancedTraversalLeafReturnPc ∧
      finish.registers 0 = entry.registers 0 ∧
      finish.registers 2 = entry.registers 2 ∧
      finish.registers 3 =
        nativeInputRequest inputLength requestCode ∧
      SameTraversalContextFrom 9 entry finish := by
  let finish :=
    (entry.write 3
      (nativeInputRequest inputLength requestCode)).jump
        balancedTraversalLeafReturnPc
  have hruns :
      RunsToIn nativeInputRequestTreeProgram maximumBits
          1 entry finish := by
    intro extra
    rw [show 1 + extra = extra + 1 by omega]
    rw [run_pair_instruction (fuel := extra)
      (value := nativeInputRequest inputLength requestCode)
      (by rfl) hpc
      (by simp [hentryLength, hatom, nativeInputRequest])
      hbits]
  refine ⟨finish, hruns, rfl, ?_, ?_, ?_, ?_⟩
  · simp [finish, hcurrent, NPOracleState.write,
      NPOracleState.jump]
  · simp [finish, NPOracleState.write, NPOracleState.jump]
  · simp [finish]
  · refine ⟨?_, ?_⟩
    · simp [finish, NPOracleState.write, NPOracleState.jump]
    · intro register hregister
      have hthree : register ≠ 3 := by omega
      simp [finish, NPOracleState.write, NPOracleState.jump, hthree]

theorem run_nativeInputRequestTreeProgram
    (inputLength : ℕ) (requestCodes : List ℕ) :
    runNPOracleProgram nativeInputRequestTreeProgram
        (nativeInputRequestTreeBits inputLength requestCodes)
        (nativeInputRequestTreeFuel requestCodes)
        (initialNPOracleState inputLength
          (encodeBalancedList requestCodes)) =
      some
        (encodeBalancedList
          (requestCodes.map (nativeInputRequest inputLength))) := by
  let initial :=
    initialNPOracleState inputLength
      (encodeBalancedList requestCodes)
  have hfit :
      BalancedTraversalFits
        (nativeInputRequestTreeBits inputLength requestCodes)
        (nativeInputRequest inputLength)
        (balancedTraversalTree requestCodes) [] :=
    (balancedTraversalRequiredBits_le_iff
      (nativeInputRequestTreeBits inputLength requestCodes)
      (nativeInputRequest inputLength)
      (balancedTraversalTree requestCodes) []).mp
        (Nat.le_max_right _ _)
  obtain ⟨finish, hruns, hpc, houtput, _hstack, _hpersistent⟩ :=
    run_balancedTraversal
      (nativeInputRequest inputLength) (fun _ => 1)
      requestCodes initial inputLength 9 (by omega)
      nativeInputRequestTreeProgram_controllerAt
      (by rfl)
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      (by simp [initial, initialNPOracleState])
      hfit
      (by
        intro requestCode _hcode entry hentryPc hcurrent
          hatom hbits hentryLength
        exact run_nativeInputRequestTreeLeaf inputLength requestCode
          (nativeInputRequestTreeBits inputLength requestCodes) entry
          hentryPc hcurrent hatom hbits hentryLength)
  have houtputBits :
      natBitLength
          (encodeBalancedList
            (requestCodes.map
              (nativeInputRequest inputLength))) ≤
        nativeInputRequestTreeBits inputLength requestCodes := by
    simpa [balancedTraversalTree_map_code] using hfit.output
  have hhalt :
      runNPOracleProgram nativeInputRequestTreeProgram
          (nativeInputRequestTreeBits inputLength requestCodes)
          1 finish =
        some
          (encodeBalancedList
            (requestCodes.map
              (nativeInputRequest inputLength))) :=
    run_halt_instruction (fuel := 0) (by rfl) hpc houtput
      houtputBits
  rw [show nativeInputRequestTreeFuel requestCodes =
      (balancedTraversalStructuralSteps
          (balancedTraversalTree requestCodes) +
        (requestCodes.map fun _ => 1).sum + 1) + 1 by
    simp [nativeInputRequestTreeFuel]]
  rw [hruns]
  exact hhalt

def balancedCallPersistentBase (callee : NPOracleProgram) : ℕ :=
  max 9 (programRegisterSpan (balancedCallProgram callee))

theorem nine_le_balancedCallPersistentBase (callee : NPOracleProgram) :
    9 ≤ balancedCallPersistentBase callee :=
  le_max_left _ _

def restoreRegistersFrom (first : ℕ) (reference state : NPOracleState) :
    NPOracleState where
  pc := state.pc
  registers := fun register =>
    if first ≤ register then
      reference.registers register
    else
      state.registers register

theorem restoreRegistersFrom_same (first : ℕ)
    (reference state : NPOracleState) :
    SameRegistersFrom first reference
      (restoreRegistersFrom first reference state) := by
  intro register hregister
  simp [restoreRegistersFrom, hregister]

theorem stateAgreesBelow_restoreRegistersFrom
    {first : ℕ} {reference state : NPOracleState} :
    StateAgreesBelow first state
      (restoreRegistersFrom first reference state) := by
  refine ⟨rfl, ?_⟩
  intro register hregister
  simp [restoreRegistersFrom, Nat.not_le.mpr hregister]

def balancedCallEntryState (callee : NPOracleProgram)
    (inputLength requestCode : ℕ) (state : NPOracleState) : NPOracleState :=
  let layout := balancedCallLayout callee
  (((zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan state).write
      (layout.calleeRegisterBase + 1) inputLength).write
      layout.calleeRegisterBase requestCode).jump layout.calleeBase

private theorem state_ext (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem jump_write (state : NPOracleState)
    (pc register value : ℕ) :
    (state.jump pc).write register value =
      (state.write register value).jump pc := by
  rfl

private theorem jump_jump (state : NPOracleState) (first second : ℕ) :
    (state.jump first).jump second = state.jump second := by
  rfl

theorem balancedCallEntryState_eq_active (callee : NPOracleProgram)
    (inputLength requestCode : ℕ) (state : NPOracleState) :
    let layout := balancedCallLayout callee
    let entry :=
      balancedCallEntryState callee inputLength requestCode state
    entry =
      relocateActiveState layout.calleeBase layout.calleeRegisterBase
        layout.calleeSpan entry.registers
        (initialNPOracleState inputLength requestCode) := by
  let layout := balancedCallLayout callee
  let entry := balancedCallEntryState callee inputLength requestCode state
  change entry =
    relocateActiveState layout.calleeBase layout.calleeRegisterBase
      layout.calleeSpan entry.registers
      (initialNPOracleState inputLength requestCode)
  apply state_ext
  · simp [entry, balancedCallEntryState, relocateActiveState,
      initialNPOracleState, layout, balancedCallLayout]
  · funext candidate
    by_cases hinside :
        layout.calleeRegisterBase ≤ candidate ∧
          candidate < layout.calleeRegisterBase + layout.calleeSpan
    · rcases hinside with ⟨hlower, hupper⟩
      by_cases hzero : candidate = layout.calleeRegisterBase
      · subst candidate
        simp [entry, balancedCallEntryState, relocateActiveState,
          initialNPOracleState, layout, balancedCallLayout]
      · by_cases hone :
          candidate = layout.calleeRegisterBase + 1
        · subst candidate
          simp [entry, balancedCallEntryState, relocateActiveState,
            initialNPOracleState, layout, balancedCallLayout]
        · have hreset :
              (zeroRegisterRange layout.calleeRegisterBase
                layout.calleeSpan state).registers candidate = 0 :=
            zeroRegisterRange_inside state hlower hupper
          have hzero' : candidate ≠ 9 := by
            simpa [layout, balancedCallLayout] using hzero
          have hone' : candidate ≠ 10 := by
            simpa [layout, balancedCallLayout] using hone
          have hlowerNine : 9 ≤ candidate := by
            simpa [layout, balancedCallLayout] using hlower
          have hsubZero : candidate - 9 ≠ 0 := by omega
          have hsubOne : candidate - 9 ≠ 1 := by omega
          have hreset' :
              (zeroRegisterRange 9 (programRegisterSpan callee) state).registers
                candidate = 0 := by
            simpa [layout, balancedCallLayout] using hreset
          simp [entry, balancedCallEntryState, relocateActiveState,
            initialNPOracleState, layout, balancedCallLayout, hzero', hone',
            hsubZero, hsubOne, hreset']
    · simp [relocateActiveState, hinside]

def balancedCallLeafBudget (callee : NPOracleProgram)
    (calleeFuel : ℕ) : ℕ :=
  (balancedCallLayout callee).calleeSpan + 2 + calleeFuel + 1

theorem run_balancedCallLeaf
    {callee : NPOracleProgram} {maximumBits atom calleeFuel output : ℕ}
    (state : NPOracleState)
    (hpc : state.pc = (balancedCallLayout callee).leafPc)
    (hcurrent : state.registers 0 = Nat.pair 1 atom)
    (hatom : state.registers 3 = atom)
    (hatomBits : natBitLength atom ≤ maximumBits)
    (houtputBits : natBitLength output ≤ maximumBits)
    (hpairBits :
      natBitLength (Nat.pair atom output) ≤ maximumBits)
    (hexec :
      runNPOracleProgram callee maximumBits calleeFuel
        (initialNPOracleState (Nat.unpair atom).1
          (Nat.unpair atom).2) = some output) :
    RunsWithin (balancedCallProgram callee) maximumBits
      (balancedCallLeafBudget callee calleeFuel) state
      (fun finish =>
        finish.pc = balancedTraversalLeafReturnPc ∧
        finish.registers 0 = state.registers 0 ∧
        finish.registers 2 = state.registers 2 ∧
        finish.registers 3 = output ∧
        SameTraversalContextFrom (balancedCallPersistentBase callee)
          state finish) := by
  let layout := balancedCallLayout callee
  let resetState :=
    (zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan
      state).jump layout.decodeBase
  let lengthState :=
    (resetState.write (layout.calleeRegisterBase + 1)
      (Nat.unpair atom).1).jump (layout.decodeBase + 1)
  let callEntry :=
    (lengthState.write layout.calleeRegisterBase
      (Nat.unpair atom).2).jump layout.calleeBase
  have hbitsPositive : 1 ≤ maximumBits := by
    have hpositive : 1 ≤ natBitLength atom := by
      unfold natBitLength
      omega
    exact hpositive.trans hatomBits
  have hleftBits :
      natBitLength (Nat.unpair atom).1 ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_left_le atom)).trans hatomBits
  have hrightBits :
      natBitLength (Nat.unpair atom).2 ≤ maximumBits :=
    (natBitLength_mono (Nat.unpair_right_le atom)).trans hatomBits
  have hstateJump :
      state.jump layout.resetBase = state := by
    cases state with
    | mk statePc registers =>
        simp only [NPOracleState.jump] at hpc ⊢
        simp only [layout, balancedCallLayout] at hpc ⊢
        subst statePc
        rfl
  have hresetWithin :
      RunsWithin (balancedCallProgram callee) maximumBits
        layout.calleeSpan state (· = resetState) := by
    intro extra finalOutput hcontinuation
    have hafter :
        runNPOracleProgram (balancedCallProgram callee) maximumBits extra
          resetState = some finalOutput := by
      simpa using hcontinuation resetState 0 rfl
    have hreset :=
      run_resetProgramAt hbitsPositive
        (balancedCallProgram_resetAt callee) hafter
    rw [hstateJump] at hreset
    simpa [layout, balancedCallLayout, resetState,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hreset
  have hresetAtom : resetState.registers 3 = atom := by
    rw [show resetState.registers 3 =
      (zeroRegisterRange layout.calleeRegisterBase layout.calleeSpan
        state).registers 3 by rfl]
    rw [zeroRegisterRange_below state (by
      simp [layout, balancedCallLayout])]
    exact hatom
  have hdecodeLeft :
      RunsToIn (balancedCallProgram callee) maximumBits 1
        resetState lengthState := by
    apply runsTo_unpairLeft
    · simpa [layout] using
        balancedCallProgram_decodeAt callee 0 (by omega)
    · simp [resetState, layout, balancedCallLayout]
    · rw [hresetAtom]
    · exact hleftBits
  have hlengthAtom : lengthState.registers 3 = atom := by
    simp [lengthState, hresetAtom, layout, balancedCallLayout]
  have hdecodeRight :
      RunsToIn (balancedCallProgram callee) maximumBits 1
        lengthState callEntry := by
    apply runsTo_unpairRight
    · simpa [layout] using
        balancedCallProgram_decodeAt callee 1 (by omega)
    · simp [lengthState, layout, balancedCallLayout]
    · rw [hlengthAtom]
    · exact hrightBits
  have hthroughDecode :
      RunsWithin (balancedCallProgram callee) maximumBits
        (layout.calleeSpan + 2) state (· = callEntry) := by
    have hthroughLeft :=
      hresetWithin.trans (fun candidate heq => by
        subst candidate
        exact hdecodeLeft.toRunsWithin)
    have hthroughRight :=
      hthroughLeft.trans (fun candidate heq => by
        subst candidate
        exact hdecodeRight.toRunsWithin)
    simpa [Nat.add_assoc] using hthroughRight
  have hcallEntry :
      callEntry =
        balancedCallEntryState callee (Nat.unpair atom).1
          (Nat.unpair atom).2 state := by
    simp [callEntry, lengthState, resetState, balancedCallEntryState,
      layout, balancedCallLayout, jump_write, jump_jump]
  have hentryActive :
      callEntry =
        relocateActiveState layout.calleeBase
          layout.calleeRegisterBase layout.calleeSpan
          callEntry.registers
          (initialNPOracleState (Nat.unpair atom).1
            (Nat.unpair atom).2) := by
    rw [hcallEntry]
    simpa [layout] using
      balancedCallEntryState_eq_active callee
        (Nat.unpair atom).1 (Nat.unpair atom).2 state
  have hentryAtom : callEntry.registers 3 = atom := by
    simp [callEntry, lengthState, hresetAtom, layout, balancedCallLayout]
  have hcalleeWithin :
      RunsWithin (balancedCallProgram callee) maximumBits
        (calleeFuel + 1) callEntry
        (fun finish =>
          finish.pc = balancedTraversalLeafReturnPc ∧
          finish.registers 0 = callEntry.registers 0 ∧
          finish.registers 2 = callEntry.registers 2 ∧
          finish.registers 3 = output ∧
          SameTraversalContextFrom (balancedCallPersistentBase callee)
            state finish) := by
    intro extra finalOutput hcontinuation
    rw [show calleeFuel + 1 + extra = calleeFuel + (1 + extra) by omega]
    rw [hentryActive]
    apply run_callable_active
      (pcOffset := layout.calleeBase)
      (registerOffset := layout.calleeRegisterBase)
      (span := layout.calleeSpan)
      (accumulatorRegister := 3)
      (returnPc := layout.returnPc)
      callEntry.registers
      (by simp [layout, balancedCallLayout])
      (le_refl layout.calleeSpan)
      (by simpa [layout] using balancedCallProgram_callableAt callee)
      hexec
    · simpa [hentryAtom] using hpairBits
    · intro haltState unused
      let atReturn :=
        (((relocateState layout.calleeBase layout.calleeRegisterBase
          callEntry.registers haltState).write 3
            (Nat.pair (callEntry.registers 3) output)).jump layout.returnPc)
      let returned :=
        (atReturn.write 3 output).jump balancedTraversalLeafReturnPc
      let restored :=
        restoreRegistersFrom (balancedCallPersistentBase callee)
          state returned
      have hreturnLookup :
          (balancedCallProgram callee)[layout.returnPc]? =
            some (.unpairRight 3 3 balancedTraversalLeafReturnPc) := by
        simpa [layout] using balancedCallProgram_return callee
      have hatReturnPc : atReturn.pc = layout.returnPc := by
        simp [atReturn]
      have hatReturnValue :
          (Nat.unpair (atReturn.registers 3)).2 = output := by
        simp [atReturn, hentryAtom]
      have hstep :
          runNPOracleProgram (balancedCallProgram callee) maximumBits
              (unused + (1 + extra)) atReturn =
            runNPOracleProgram (balancedCallProgram callee) maximumBits
              (unused + extra) returned := by
        rw [show unused + (1 + extra) = (unused + extra) + 1 by omega]
        simp only [runNPOracleProgram]
        rw [hatReturnPc, hreturnLookup]
        simp only
        rw [show atReturn.boundedWrite maximumBits 3
              (Nat.unpair (atReturn.registers 3)).2 =
            some (atReturn.write 3 output) by
          simp [NPOracleState.boundedWrite, hatReturnValue, houtputBits]]
      rw [hstep]
      have hagrees :
          StateAgreesBelow
            (programRegisterSpan (balancedCallProgram callee))
            returned restored := by
        have hfull :=
          stateAgreesBelow_restoreRegistersFrom
          (first := balancedCallPersistentBase callee)
          (reference := state)
          (state := returned) |>.2
        refine ⟨rfl, ?_⟩
        intro register hregister
        apply hfull
        exact hregister.trans_le (le_max_right _ _)
      rw [run_congr_of_stateAgreesBelow
        (le_refl (programRegisterSpan (balancedCallProgram callee)))
        hagrees]
      apply hcontinuation restored unused
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [restored, restoreRegistersFrom, returned]
      · simp [restored, restoreRegistersFrom, returned, atReturn,
          relocateState, balancedCallPersistentBase, layout,
          balancedCallLayout]
      · simp [restored, restoreRegistersFrom, returned, atReturn,
          relocateState, balancedCallPersistentBase, layout,
          balancedCallLayout]
      · simp [restored, restoreRegistersFrom, returned, atReturn,
          balancedCallPersistentBase, layout, balancedCallLayout]
      · refine ⟨?_, restoreRegistersFrom_same _ _ _⟩
        have hbelow :
            (zeroRegisterRange 9 (programRegisterSpan callee) state).registers
                1 =
              state.registers 1 :=
          zeroRegisterRange_below state (by omega)
        simpa [restored, restoreRegistersFrom, returned, atReturn,
          relocateState, callEntry, lengthState, resetState,
          balancedCallPersistentBase, layout, balancedCallLayout] using
          hbelow
  have htotal :=
    hthroughDecode.trans (fun candidate heq => by
      subst candidate
      exact hcalleeWithin)
  have hentryZero : callEntry.registers 0 = state.registers 0 := by
    simp only [callEntry, lengthState, resetState, NPOracleState.jump,
      NPOracleState.write]
    rw [zeroRegisterRange_below state (by
      simp [layout, balancedCallLayout])]
    simp [layout, balancedCallLayout]
  have hentryTwo : callEntry.registers 2 = state.registers 2 := by
    simp only [callEntry, lengthState, resetState, NPOracleState.jump,
      NPOracleState.write]
    rw [zeroRegisterRange_below state (by
      simp [layout, balancedCallLayout])]
    simp [layout, balancedCallLayout]
  apply htotal.mono
  · intro finish hfinish
    refine ⟨hfinish.1, ?_, ?_, hfinish.2.2.2.1, ?_⟩
    · rw [hfinish.2.1, hentryZero]
    · rw [hfinish.2.2.1, hentryTwo]
    · exact hfinish.2.2.2.2

def balancedCallFuel (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ) (requests : List ℕ) : ℕ :=
  balancedTraversalStructuralSteps (balancedTraversalTree requests) +
    (requests.map fun request =>
      balancedCallLeafBudget callee (calleeFuel request)).sum + 2

def balancedCallRequiredBits (output : ℕ → ℕ)
    (requests : List ℕ) : ℕ :=
  max
    (balancedTraversalRequiredBits output
      (balancedTraversalTree requests) [])
    ((requests.map fun request =>
      natBitLength (Nat.pair request (output request))).foldr max 0)

/-- Polynomial atom-width envelope for both sides of a balanced call. -/
def balancedCallValueBits (output : ℕ → ℕ)
    (requests : List ℕ) : ℕ :=
  max
    (1 + 2 * requests.length ^ 4 * balancedListAtomBits requests)
    (1 + 2 * requests.length ^ 4 *
      balancedListAtomBits (requests.map output))

/-- Explicit width sufficient for every balanced-call tree, continuation
stack, leaf atom, output atom, and request/output return pair.  The fixed
exponents are independent of the request family. -/
def balancedCallPolynomialBits (output : ℕ → ℕ)
    (requests : List ℕ) : ℕ :=
  let valueBits := balancedCallValueBits output requests
  max (2 * valueBits)
    (16 * (requests.length + 1) ^ 2 *
      ((requests.length + 1) * (2 * valueBits) + 1))

private theorem balancedListHeight_le_length_succ
    (values : List ℕ) :
    balancedListHeight values ≤ values.length + 1 := by
  calc
    balancedListHeight values ≤
        Nat.clog 2 values.length + 1 :=
      balancedListHeight_le_clog values
    _ ≤ values.length + 1 := by
      apply Nat.add_le_add_right
      exact Nat.clog_le_of_le_pow
        (Nat.le_of_lt values.length.lt_two_pow_self)

private theorem balancedTraversalStackAtomBits_le
    (frames : List BalancedTraversalFrame) (valueBits : ℕ)
    (hframe :
      ∀ frame, frame ∈ frames →
        natBitLength (encodeBalancedTraversalFrame frame) ≤
          2 * valueBits) :
    balancedTraversalStackAtomBits frames ≤
      frames.length * (2 * valueBits) + 1 := by
  unfold balancedTraversalStackAtomBits taggedControlAtomBits
  rw [List.map_map]
  induction frames with
  | nil => simp
  | cons frame frames inductionHypothesis =>
      have hhead := hframe frame (by simp)
      have htail :
          ∀ candidate, candidate ∈ frames →
            natBitLength (encodeBalancedTraversalFrame candidate) ≤
              2 * valueBits := by
        intro candidate hcandidate
        exact hframe candidate (by simp [hcandidate])
      have hrest := inductionHypothesis htail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        natBitLength (encodeBalancedTraversalFrame frame) +
              (List.map (natBitLength ∘ encodeBalancedTraversalFrame)
                frames).sum + 1 ≤
            2 * valueBits + frames.length * (2 * valueBits) + 1 := by
          omega
        _ = (frames.length + 1) * (2 * valueBits) + 1 := by
          ring

private theorem frame_bits_le_twice
    {valueBits data : ℕ} (hpositive : 1 ≤ valueBits)
    (hdata : natBitLength data ≤ valueBits)
    (frame : BalancedTraversalFrame)
    (hframe :
      frame = .visitRight data ∨ frame = .combineLeft data) :
    natBitLength (encodeBalancedTraversalFrame frame) ≤
      2 * valueBits := by
  rcases hframe with rfl | rfl
  · apply (pairCodeBits_le 0 data).trans
    apply Nat.mul_le_mul_left
    apply max_le
    · norm_num [natBitLength]
      exact hpositive
    · exact hdata
  · apply (pairCodeBits_le 1 data).trans
    apply Nat.mul_le_mul_left
    apply max_le
    · norm_num [natBitLength]
      exact hpositive
    · exact hdata

private theorem balancedTraversalFits_polynomial
    (output : ℕ → ℕ) (requests : List ℕ)
    (tree : BalancedTraversalTree)
    (frames : List BalancedTraversalFrame)
    (valueBits : ℕ)
    (hpositive : 1 ≤ valueBits)
    (hinput : natBitLength tree.code ≤ valueBits)
    (houtput : natBitLength (tree.map output).code ≤ valueBits)
    (hdepth :
      frames.length + tree.height ≤ balancedListHeight requests)
    (hframes :
      ∀ frame, frame ∈ frames →
        natBitLength (encodeBalancedTraversalFrame frame) ≤
          2 * valueBits) :
    BalancedTraversalFits
      (max (2 * valueBits)
        (16 * (requests.length + 1) ^ 2 *
          ((requests.length + 1) * (2 * valueBits) + 1)))
      output tree frames := by
  let polynomialBits :=
    max (2 * valueBits)
      (16 * (requests.length + 1) ^ 2 *
        ((requests.length + 1) * (2 * valueBits) + 1))
  have hvalueBits : valueBits ≤ polynomialBits := by
    apply le_max_of_le_left
    omega
  have hheight := balancedListHeight_le_length_succ requests
  have stackFits :
      ∀ candidateFrames : List BalancedTraversalFrame,
        (∀ frame, frame ∈ candidateFrames →
          natBitLength (encodeBalancedTraversalFrame frame) ≤
            2 * valueBits) →
        candidateFrames.length ≤ balancedListHeight requests →
        natBitLength (encodeBalancedTraversalStack candidateFrames) ≤
          polynomialBits := by
    intro candidateFrames hcandidateFrames hcandidateDepth
    have hstackAtom :=
      balancedTraversalStackAtomBits_le candidateFrames valueBits
        hcandidateFrames
    have hatomBound :
        balancedTraversalStackAtomBits candidateFrames ≤
          (requests.length + 1) * (2 * valueBits) + 1 := by
      exact hstackAtom.trans <|
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (2 * valueBits)
            (hcandidateDepth.trans hheight)) 1
    apply (balancedTraversalStackBits_polynomial
      candidateFrames requests hcandidateDepth).trans
    apply le_max_of_le_right
    exact Nat.mul_le_mul_left
      (16 * (requests.length + 1) ^ 2) hatomBound
  induction tree generalizing frames with
  | empty =>
      have hstack := stackFits frames hframes (by omega)
      unfold BalancedTraversalFits
      exact ⟨hinput.trans hvalueBits, houtput.trans hvalueBits,
        hstack, trivial⟩
  | leaf atom =>
      have hstack := stackFits frames hframes (by omega)
      have hatom :
          natBitLength atom ≤ valueBits := by
        apply (natBitLength_mono (Nat.right_le_pair 1 atom)).trans
        simpa [BalancedTraversalTree.code] using hinput
      have hmapped :
          natBitLength (output atom) ≤ valueBits := by
        apply
          (natBitLength_mono
            (Nat.right_le_pair 1 (output atom))).trans
        simpa [BalancedTraversalTree.map,
          BalancedTraversalTree.code] using houtput
      unfold BalancedTraversalFits
      exact ⟨hinput.trans hvalueBits, houtput.trans hvalueBits,
        hstack, hatom.trans hvalueBits, hmapped.trans hvalueBits⟩
  | branch left right inductionLeft inductionRight =>
      have hleftInput :
          natBitLength left.code ≤ valueBits := by
        apply (natBitLength_mono ?_).trans hinput
        simp only [BalancedTraversalTree.code]
        exact
          (Nat.left_le_pair left.code right.code).trans
            (Nat.right_le_pair 2 (Nat.pair left.code right.code))
      have hrightInput :
          natBitLength right.code ≤ valueBits := by
        apply (natBitLength_mono ?_).trans hinput
        simp only [BalancedTraversalTree.code]
        exact
          (Nat.right_le_pair left.code right.code).trans
            (Nat.right_le_pair 2 (Nat.pair left.code right.code))
      have hleftOutput :
          natBitLength (left.map output).code ≤ valueBits := by
        apply (natBitLength_mono ?_).trans houtput
        simp only [BalancedTraversalTree.map, BalancedTraversalTree.code]
        exact
          (Nat.left_le_pair (left.map output).code
              (right.map output).code).trans
            (Nat.right_le_pair 2
              (Nat.pair (left.map output).code
                (right.map output).code))
      have hrightOutput :
          natBitLength (right.map output).code ≤ valueBits := by
        apply (natBitLength_mono ?_).trans houtput
        simp only [BalancedTraversalTree.map, BalancedTraversalTree.code]
        exact
          (Nat.right_le_pair (left.map output).code
              (right.map output).code).trans
            (Nat.right_le_pair 2
              (Nat.pair (left.map output).code
                (right.map output).code))
      have hleftDepth :
          (.visitRight right.code :: frames).length + left.height ≤
            balancedListHeight requests := by
        have hleftHeight : left.height ≤ max left.height right.height :=
          le_max_left _ _
        simp only [BalancedTraversalTree.height] at hdepth
        simp only [List.length_cons]
        omega
      have hrightDepth :
          (.combineLeft (left.map output).code :: frames).length +
              right.height ≤ balancedListHeight requests := by
        have hrightHeight : right.height ≤ max left.height right.height :=
          le_max_right _ _
        simp only [BalancedTraversalTree.height] at hdepth
        simp only [List.length_cons]
        omega
      have hleftFrames :
          ∀ frame,
            frame ∈ (.visitRight right.code :: frames) →
              natBitLength (encodeBalancedTraversalFrame frame) ≤
                2 * valueBits := by
        intro frame hframe
        rcases List.mem_cons.mp hframe with rfl | hframe
        · exact frame_bits_le_twice hpositive hrightInput _
            (Or.inl rfl)
        · exact hframes frame hframe
      have hrightFrames :
          ∀ frame,
            frame ∈
                (.combineLeft (left.map output).code :: frames) →
              natBitLength (encodeBalancedTraversalFrame frame) ≤
                2 * valueBits := by
        intro frame hframe
        rcases List.mem_cons.mp hframe with rfl | hframe
        · exact frame_bits_le_twice hpositive hleftOutput _
            (Or.inr rfl)
        · exact hframes frame hframe
      have hleftFit :=
        inductionLeft
          (.visitRight right.code :: frames)
          hleftInput hleftOutput hleftDepth hleftFrames
      have hrightFit :=
        inductionRight
          (.combineLeft (left.map output).code :: frames)
          hrightInput hrightOutput hrightDepth hrightFrames
      have hstack := stackFits frames hframes (by omega)
      unfold BalancedTraversalFits
      exact ⟨hinput.trans hvalueBits, houtput.trans hvalueBits,
        hstack, hleftFit, hrightFit⟩

private theorem natBitLength_le_balancedListAtomBits
    {value : ℕ} {values : List ℕ} (hvalue : value ∈ values) :
    natBitLength value ≤ balancedListAtomBits values := by
  unfold balancedListAtomBits
  have hmember :
      natBitLength value ∈ values.map natBitLength :=
    List.mem_map.mpr ⟨value, hvalue, rfl⟩
  exact
    (List.le_sum_of_mem hmember).trans
      (Nat.le_add_right _ _)

private theorem foldr_max_le
    {values : List ℕ} {bound : ℕ}
    (hbound : ∀ value, value ∈ values → value ≤ bound) :
    values.foldr max 0 ≤ bound := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      simp only [List.foldr]
      apply max_le
      · exact hbound value (by simp)
      · apply inductionHypothesis
        intro candidate hcandidate
        exact hbound candidate (by simp [hcandidate])

/-- The exact balanced-call register requirement is bounded by one fixed
polynomial in request count and the total bit width of request/output atoms.
This is the production resource closure: no linked-list code or
depth-dependent premise survives in the theorem statement. -/
theorem balancedCallRequiredBits_le_polynomial
    (output : ℕ → ℕ) (requests : List ℕ) :
    balancedCallRequiredBits output requests ≤
      balancedCallPolynomialBits output requests := by
  let valueBits := balancedCallValueBits output requests
  have hpositive : 1 ≤ valueBits := by
    unfold valueBits balancedCallValueBits
    omega
  have hinput :
      natBitLength (balancedTraversalTree requests).code ≤
        valueBits := by
    rw [balancedTraversalTree_code]
    exact (balancedListCodeBits_le requests).trans (le_max_left _ _)
  have houtput :
      natBitLength
          ((balancedTraversalTree requests).map output).code ≤
        valueBits := by
    rw [balancedTraversalTree_map_code]
    apply (balancedListCodeBits_le (requests.map output)).trans
    dsimp [valueBits, balancedCallValueBits]
    simpa only [List.length_map] using
      (le_max_right
        (1 + 2 * requests.length ^ 4 *
          balancedListAtomBits requests)
        (1 + 2 * requests.length ^ 4 *
          balancedListAtomBits (requests.map output)))
  have hdepth :
      ([] : List BalancedTraversalFrame).length +
          (balancedTraversalTree requests).height ≤
        balancedListHeight requests := by
    simp [balancedTraversalTree_height_eq]
  have hfit :
      BalancedTraversalFits
        (balancedCallPolynomialBits output requests)
        output (balancedTraversalTree requests) [] := by
    simpa [balancedCallPolynomialBits, valueBits] using
      balancedTraversalFits_polynomial output requests
        (balancedTraversalTree requests) [] valueBits
        hpositive hinput houtput hdepth (by simp)
  have htraversal :
      balancedTraversalRequiredBits output
          (balancedTraversalTree requests) [] ≤
        balancedCallPolynomialBits output requests :=
    (balancedTraversalRequiredBits_le_iff
      (balancedCallPolynomialBits output requests) output
      (balancedTraversalTree requests) []).mpr hfit
  have hatom :
      ∀ request, request ∈ requests →
        natBitLength request ≤ valueBits := by
    intro request hrequest
    have hlength : 1 ≤ requests.length :=
      (List.length_pos_iff_ne_nil.mpr (List.ne_nil_of_mem hrequest))
    have hfactor : 1 ≤ 2 * requests.length ^ 4 := by
      have hpower : 1 ≤ requests.length ^ 4 :=
        Nat.one_le_pow 4 requests.length hlength
      nlinarith
    apply (natBitLength_le_balancedListAtomBits hrequest).trans
    apply le_max_of_le_left
    have hscale := Nat.mul_le_mul_right
      (balancedListAtomBits requests) hfactor
    omega
  have hmapped :
      ∀ request, request ∈ requests →
        natBitLength (output request) ≤ valueBits := by
    intro request hrequest
    have hlength : 1 ≤ requests.length :=
      (List.length_pos_iff_ne_nil.mpr (List.ne_nil_of_mem hrequest))
    have hfactor : 1 ≤ 2 * requests.length ^ 4 := by
      have hpower : 1 ≤ requests.length ^ 4 :=
        Nat.one_le_pow 4 requests.length hlength
      nlinarith
    have hmember :
        output request ∈ requests.map output :=
      List.mem_map.mpr ⟨request, hrequest, rfl⟩
    apply
      (natBitLength_le_balancedListAtomBits hmember).trans
    apply le_max_of_le_right
    have hscale := Nat.mul_le_mul_right
      (balancedListAtomBits (requests.map output)) hfactor
    omega
  have hpairs :
      (requests.map fun request =>
          natBitLength (Nat.pair request (output request))).foldr max 0 ≤
        2 * valueBits := by
    apply foldr_max_le
    intro pairBits hpairBits
    rcases List.mem_map.mp hpairBits with ⟨request, hrequest, rfl⟩
    apply (pairCodeBits_le request (output request)).trans
    apply Nat.mul_le_mul_left
    exact max_le (hatom request hrequest) (hmapped request hrequest)
  unfold balancedCallRequiredBits balancedCallPolynomialBits
  apply max_le
  · exact htraversal
  · exact hpairs.trans (le_max_left _ _)

theorem balancedCallFuel_positive (callee : NPOracleProgram)
    (calleeFuel : ℕ → ℕ) (requests : List ℕ) :
    0 < balancedCallFuel callee calleeFuel requests := by
  unfold balancedCallFuel
  omega

theorem one_le_balancedCallRequiredBits
    (output : ℕ → ℕ) (requests : List ℕ) :
    1 ≤ balancedCallRequiredBits output requests := by
  have hpositive :
      1 ≤ natBitLength (balancedTraversalTree requests).code := by
    unfold natBitLength
    omega
  have hinput :
      natBitLength (balancedTraversalTree requests).code ≤
        balancedTraversalRequiredBits output
          (balancedTraversalTree requests) [] := by
    unfold balancedTraversalRequiredBits
    exact le_max_left _ _
  exact hpositive.trans <| hinput.trans <| le_max_left _ _

private theorem le_foldr_max_of_mem {value : ℕ} {values : List ℕ}
    (hmem : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldr]
      rcases hmem with rfl | hmem
      · exact le_max_left _ _
      · exact (ih hmem).trans (le_max_right _ _)

theorem balancedCallRequiredBits_traversal
    (output : ℕ → ℕ) (requests : List ℕ) :
    balancedTraversalRequiredBits output
        (balancedTraversalTree requests) [] ≤
      balancedCallRequiredBits output requests :=
  le_max_left _ _

theorem balancedCallRequiredBits_request
    (output : ℕ → ℕ) {requests : List ℕ} {request : ℕ}
    (hmem : request ∈ requests) :
    natBitLength request ≤ balancedCallRequiredBits output requests := by
  have htreeMem : request ∈ (balancedTraversalTree requests).atoms := by
    simpa [balancedTraversalTree_atoms] using hmem
  exact
    (balancedTraversalRequiredBits_atom
      (f := output) (frames := []) htreeMem).trans
      (balancedCallRequiredBits_traversal output requests)

theorem balancedCallRequiredBits_pair
    (output : ℕ → ℕ) {requests : List ℕ} {request : ℕ}
    (hmem : request ∈ requests) :
    natBitLength (Nat.pair request (output request)) ≤
      balancedCallRequiredBits output requests := by
  apply (le_foldr_max_of_mem (values := requests.map fun candidate =>
      natBitLength (Nat.pair candidate (output candidate))) ?_).trans
    (le_max_right _ _)
  exact List.mem_map.mpr ⟨request, hmem, rfl⟩

theorem balancedCallFuel_le_linearController
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (requests : List ℕ) :
    balancedCallFuel callee calleeFuel requests ≤
      35 * (2 * requests.length + 1) +
        (requests.map fun request =>
          balancedCallLeafBudget callee (calleeFuel request)).sum + 2 := by
  unfold balancedCallFuel
  exact Nat.add_le_add_right
    (Nat.add_le_add_right
      (balancedTraversalStructuralSteps_le_linear requests) _) _

private theorem balancedCallLeafBudget_sum_le
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (requests : List ℕ) (fuelBound : ℕ)
    (hbound :
      ∀ request, request ∈ requests → calleeFuel request ≤ fuelBound) :
    (requests.map fun request =>
        balancedCallLeafBudget callee (calleeFuel request)).sum ≤
      requests.length * balancedCallLeafBudget callee fuelBound := by
  induction requests with
  | nil => simp
  | cons request rest ih =>
      have hhead := hbound request (by simp)
      have htail :
          ∀ candidate, candidate ∈ rest →
            calleeFuel candidate ≤ fuelBound := by
        intro candidate hmem
        exact hbound candidate (by simp [hmem])
      have hrest := ih htail
      calc
        ((request :: rest).map fun candidate =>
              balancedCallLeafBudget callee
                (calleeFuel candidate)).sum =
            balancedCallLeafBudget callee (calleeFuel request) +
              (rest.map fun candidate =>
                balancedCallLeafBudget callee
                  (calleeFuel candidate)).sum := by simp
        _ ≤ balancedCallLeafBudget callee fuelBound +
              rest.length *
                balancedCallLeafBudget callee fuelBound := by
          apply Nat.add_le_add
          · unfold balancedCallLeafBudget
            omega
          · exact hrest
        _ = (request :: rest).length *
              balancedCallLeafBudget callee fuelBound := by
          simp only [List.length_cons]
          ring

theorem balancedCallFuel_le_uniform
    (callee : NPOracleProgram) (calleeFuel : ℕ → ℕ)
    (requests : List ℕ) (fuelBound : ℕ)
    (hbound :
      ∀ request, request ∈ requests → calleeFuel request ≤ fuelBound) :
    balancedCallFuel callee calleeFuel requests ≤
      35 * (2 * requests.length + 1) +
        requests.length * balancedCallLeafBudget callee fuelBound + 2 := by
  unfold balancedCallFuel
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact balancedTraversalStructuralSteps_le_linear requests
  · exact balancedCallLeafBudget_sum_le callee calleeFuel requests
      fuelBound hbound

/-- End-to-end balanced call theorem.  The callee fuel may vary by request and
is only an upper bound; the resulting program has one canonical list ABI and
returns the balanced output list directly. -/
theorem run_balancedCallProgram_from
    {callee : NPOracleProgram} {maximumBits : ℕ}
    (inputLength : ℕ) (requests : List ℕ)
    (calleeFuel output : ℕ → ℕ)
    (hrequired :
      balancedCallRequiredBits output requests ≤ maximumBits)
    (hexec :
      ∀ request, request ∈ requests →
        runNPOracleProgram callee maximumBits (calleeFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) = some (output request)) :
    runNPOracleProgram (balancedCallProgram callee) maximumBits
        (balancedCallFuel callee calleeFuel requests)
        (initialNPOracleState inputLength
          (encodeBalancedList requests)) =
      some (encodeBalancedList (requests.map output)) := by
  let start :=
    initialNPOracleState inputLength (encodeBalancedList requests)
  have hfit :
      BalancedTraversalFits maximumBits output
        (balancedTraversalTree requests) [] :=
    (balancedTraversalRequiredBits_le_iff maximumBits output
      (balancedTraversalTree requests) []).mp
        ((balancedCallRequiredBits_traversal output requests).trans hrequired)
  have hhandler :
      ∀ atom, atom ∈ requests →
        ∀ entry : NPOracleState,
          entry.pc = (balancedCallLayout callee).leafPc →
          entry.registers 0 = Nat.pair 1 atom →
          entry.registers 3 = atom →
          natBitLength (output atom) ≤ maximumBits →
          entry.registers 1 = inputLength →
          RunsWithin (balancedCallProgram callee) maximumBits
            (balancedCallLeafBudget callee (calleeFuel atom)) entry
            (fun finish =>
              finish.pc = balancedTraversalLeafReturnPc ∧
              finish.registers 0 = entry.registers 0 ∧
              finish.registers 2 = entry.registers 2 ∧
              finish.registers 3 = output atom ∧
              SameTraversalContextFrom (balancedCallPersistentBase callee)
                entry finish) := by
    intro atom hmem entry hpc hcurrent hatom houtput
      _hentryInputLength
    exact run_balancedCallLeaf entry hpc hcurrent hatom
      ((balancedCallRequiredBits_request output hmem).trans hrequired)
      houtput
      ((balancedCallRequiredBits_pair output hmem).trans hrequired)
      (hexec atom hmem)
  have htraversal :=
    run_balancedTraversalWithin output
      (fun request =>
        balancedCallLeafBudget callee (calleeFuel request))
      requests start inputLength
      (balancedCallPersistentBase callee)
      (nine_le_balancedCallPersistentBase callee)
      (balancedCallProgram_controllerAt callee)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      hfit hhandler
  have hfinalBits :
      natBitLength (encodeBalancedList (requests.map output)) ≤
        maximumBits := by
    have hmapped := hfit.output
    rw [balancedTraversalTree_map_code] at hmapped
    exact hmapped
  unfold RunsWithin at htraversal
  have hrun :=
    htraversal 1 (encodeBalancedList (requests.map output)) (by
      intro finish unused hfinish
      rw [show unused + 1 = unused + 1 by rfl]
      simp only [runNPOracleProgram]
      rw [hfinish.1, balancedCallProgram_halt callee]
      simp [hfinish.2.1, hfinalBits])
  simpa [balancedCallFuel, start, Nat.add_assoc] using hrun

theorem run_balancedCallProgram
    {callee : NPOracleProgram} {maximumBits : ℕ}
    (requests : List ℕ) (calleeFuel output : ℕ → ℕ)
    (hrequired :
      balancedCallRequiredBits output requests ≤ maximumBits)
    (hexec :
      ∀ request, request ∈ requests →
        runNPOracleProgram callee maximumBits (calleeFuel request)
          (initialNPOracleState (Nat.unpair request).1
            (Nat.unpair request).2) = some (output request)) :
    runNPOracleProgram (balancedCallProgram callee) maximumBits
        (balancedCallFuel callee calleeFuel requests)
        (initialNPOracleState requests.length
          (encodeBalancedList requests)) =
      some (encodeBalancedList (requests.map output)) := by
  exact run_balancedCallProgram_from requests.length requests
    calleeFuel output hrequired hexec

end NearCubicWires.CanonicalBalancedCall
