import Proof.Supplier.SelectiveUniversalOutputRun
import Proof.Supplier.SelectiveClauseRun
import Batteries.Tactic.OpenPrivate

/-!
# The projected query compiler's run

`selectiveUniversalOutputsProgram` is the `1256`-instruction stream that
compiles every projected query of one verifier row.  It is a controller of `60`
instructions with three relocated callees: the `276`-instruction address
evaluator, the `909`-instruction universal-evaluator output compiler and the
`11`-instruction tagged reverse pass.

The controller is a loop.  Both cursors are monotone — the row-major table
cursor in register `24` advances by one query width per iteration and the
countdown in register `18` falls — while live query wires stay on one private
reverse spine in register `26`.  Only the exit reverses that spine, because the
clause compiler one level up consumes the queries in forward order.  The
controller therefore returns a wire *list*: the compiler state beside the
encoded forward list of query wires.

This module executes that controller.  The reverse pass is consumed opaquely
through its entry-independent run; the address evaluator and the output
compiler are named runner premises one level down.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralTableCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveUniversalOutputsInput
  selectiveUniversalOutputsControllerProgram
  selectiveUniversalOutputsControllerProgram_length
  selectiveUniversalOutputsProgram selectiveUniversalOutputInput
  selectiveUniversalOutputProgram selectiveUniversalOutputProgram_length
  structuralAddressInput structuralAddressProgram
  structuralAddressProgram_length structuralTaggedReverseProgram
  structuralTaggedReverseFuel structuralTaggedReverseBits from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

open private selectiveCompileUniversalOutput_ordered from
  Proof.Supplier.SelectiveCountCasesRun

/-! ## 1. Decoding the fixed 1256-instruction stream

The controller occupies the first `60` positions, the address evaluator the
next `276`, the output compiler the next `909` and the reverse pass the last
`11`.  Every later step decodes through exactly one of the four lemmas
below. -/

private theorem structuralTaggedReverseProgram_length_eq' :
    structuralTaggedReverseProgram.length = 11 := by
  rfl

private theorem jump_registers_eq' (state : NPOracleState)
    (target index : ℕ) :
    (state.jump target).registers index = state.registers index :=
  rfl

private theorem selectiveUniversalOutputsProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveUniversalOutputsControllerProgram 60 336 1245)[pc]? =
        some instruction) :
    selectiveUniversalOutputsProgram[pc]? = some instruction := by
  have hpc :
      pc < (selectiveUniversalOutputsControllerProgram 60 336 1245).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUniversalOutputsControllerProgram_length] at hpc
  simp only [selectiveUniversalOutputsProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length,
      selectiveUniversalOutputProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveUniversalOutputsControllerProgram_length]
    omega)]
  exact hlookup

private theorem selectiveUniversalOutputsProgram_addressCallable :
    ProgramCallableAt selectiveUniversalOutputsProgram structuralAddressProgram
      60 1000 50 28 := by
  intro pc instruction hlookup
  have hpc : pc < structuralAddressProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralAddressProgram_length] at hpc
  simp only [selectiveUniversalOutputsProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length,
      selectiveUniversalOutputProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveUniversalOutputsControllerProgram_length]
    omega)]
  simp only [selectiveUniversalOutputsControllerProgram_length]
  rw [show 60 + pc - 60 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveUniversalOutputsProgram_outputCallable :
    ProgramCallableAt selectiveUniversalOutputsProgram
      selectiveUniversalOutputProgram 336 5000 50 40 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUniversalOutputProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUniversalOutputProgram_length] at hpc
  simp only [selectiveUniversalOutputsProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length,
      selectiveUniversalOutputProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalOutputsControllerProgram_length,
    structuralAddressProgram_length]
  rw [show 336 + pc - (60 + 276) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveUniversalOutputsProgram_reverseCallable :
    ProgramCallableAt selectiveUniversalOutputsProgram
      structuralTaggedReverseProgram 1245 22000 50 55 := by
  intro pc instruction hlookup
  have hpc : pc < structuralTaggedReverseProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralTaggedReverseProgram_length_eq'] at hpc
  simp only [selectiveUniversalOutputsProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputsControllerProgram_length,
      structuralAddressProgram_length,
      selectiveUniversalOutputProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalOutputsControllerProgram_length,
    structuralAddressProgram_length, selectiveUniversalOutputProgram_length]
  rw [show 1245 + pc - (60 + 276 + 909) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 2. The controller's loop, at the typed level

The source compiler's query list recurses from the front, which is exactly the
order the controller visits its queries in, so the loop needs only the standing
fact that the abstract address list it carries is the projected list from the
current cursor onward. -/

/-- Encoded compiler wire list: the encoded selective state beside the encoded
forward list of retained wires.  This is the shape the projected query
compiler returns and the clause compiler one level up consumes. -/
def selectiveWireListCode {n : ℕ} (wires : SelectiveWireList n) : ℕ :=
  Nat.pair (selectiveStateCode wires.state) (encodeTaggedList wires.values)

/-- The controller visits projected queries in ascending order from a fixed
row-major cursor. -/
private def SelectiveQueriesFrom (outputs : List ℕ)
    (width randomnessCode : ℕ) : ℕ → List (BitInput width) → Prop
  | _, [] => True
  | start, address :: rest =>
      address =
          projectionTableAddress outputs width start
            (tableRandomness width randomnessCode) ∧
        SelectiveQueriesFrom outputs width randomnessCode (start + 1) rest

private theorem selectiveQueriesFrom_ofFn (outputs : List ℕ)
    (width randomnessCode : ℕ) :
    ∀ (length start : ℕ) (index : Fin length → ℕ),
      (∀ position : Fin length, index position = start + position.val) →
      SelectiveQueriesFrom outputs width randomnessCode start
        (List.ofFn fun position : Fin length =>
          projectionTableAddress outputs width (index position)
            (tableRandomness width randomnessCode))
  | 0, _, _, _ => by
      simp only [List.ofFn_zero]
      exact trivial
  | length + 1, start, index, hindex => by
      rw [List.ofFn_succ]
      refine ⟨by rw [hindex 0]; simp, ?_⟩
      refine selectiveQueriesFrom_ofFn outputs width randomnessCode length
        (start + 1) (fun position => index position.succ) ?_
      intro position
      have hposition := hindex position.succ
      simp only [Fin.val_succ] at hposition
      omega

/-- The wire list the controller returns from the loop head. -/
private def universalOutputsOutput {width bound : ℕ} (nodeCount : ℕ)
    (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound)) (values : List ℕ)
    (addresses : List (BitInput width)) : ℕ :=
  Nat.pair
    (selectiveStateCode
      (selectiveCompileUniversalOutputs state nodeCount hnodeCount
        addresses).state)
    (encodeTaggedList
      (values ++
        (selectiveCompileUniversalOutputs state nodeCount hnodeCount
          addresses).values))

private theorem universalOutputsOutput_nil {width bound : ℕ} (nodeCount : ℕ)
    (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound))
    (values : List ℕ) :
    universalOutputsOutput nodeCount hnodeCount state values [] =
      Nat.pair (selectiveStateCode state) (encodeTaggedList values) := by
  simp only [universalOutputsOutput, selectiveCompileUniversalOutputs,
    List.append_nil]

private theorem universalOutputsOutput_cons {width bound : ℕ} (nodeCount : ℕ)
    (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound))
    (values : List ℕ) (address : BitInput width)
    (rest : List (BitInput width)) :
    universalOutputsOutput nodeCount hnodeCount state values
        (address :: rest) =
      universalOutputsOutput nodeCount hnodeCount
        (selectiveCompileUniversalOutput state address nodeCount
          hnodeCount).state
        (values ++
          [(selectiveCompileUniversalOutput state address nodeCount
            hnodeCount).output]) rest := by
  simp only [universalOutputsOutput, selectiveCompileUniversalOutputs,
    List.append_assoc, List.singleton_append]

/-! ## 3. The three call frames

Each relocated call is one physical block: the controller builds the callee's
request in place, zeroes the shared accumulator, jumps to the callee base and
unpacks the returned value.  Every frame consumes its callee's run as a
hypothesis.

The controller writes register `29` at `48` to hold the spine's cons tag, so
from the second iteration onward the branch register at every call site is
nonzero.  All three call sites and the loop's back edge branch to the same
target either way, so no step here decides on it. -/

-- Six request steps around the relocated address evaluator, then one unpacking
-- step and one cursor step.
private theorem run_selectiveUniversalOutputsAddressCall {width : ℕ}
    (address : BitInput width)
    (table inputArity rowWidthValue fieldLimit stateRemaining next selected
      remaining nodeCount randomnessCode processed spine : ℕ)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        structuralAddressInput table width randomnessCode
          (projectionQueryOffset width processed 0) →
      runNPOracleProgram structuralAddressProgram maximumBits calleeFuel
          frame =
        some (encodeBitInput address))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (structuralAddressInput table width randomnessCode
            (projectionQueryOffset width processed 0)) ≤
        maximumBits)
    (hpairBits :
      natBitLength (Nat.pair 0 (encodeBitInput address)) ≤ maximumBits)
    (hcursorBits :
      natBitLength (projectionQueryOffset width (processed + 1) 0) ≤
        maximumBits)
    (hpc : machine.pc = 22)
    (hstateRemaining : machine.registers 4 = stateRemaining)
    (hnext : machine.registers 6 = next)
    (hselected : machine.registers 7 = selected)
    (htable : machine.registers 8 = table)
    (harity : machine.registers 10 = inputArity)
    (hrowWidth : machine.registers 12 = rowWidthValue)
    (hfieldLimit : machine.registers 14 = fieldLimit)
    (hwidth : machine.registers 16 = width)
    (hcount : machine.registers 18 = remaining + 1)
    (hnodeCount : machine.registers 20 = nodeCount)
    (hrandomness : machine.registers 22 = randomnessCode)
    (hcursor :
      machine.registers 24 = projectionQueryOffset width processed 0)
    (hspine : machine.registers 26 = spine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 30 →
      resumed.registers 4 = stateRemaining →
      resumed.registers 6 = next →
      resumed.registers 7 = selected →
      resumed.registers 8 = table →
      resumed.registers 10 = inputArity →
      resumed.registers 12 = rowWidthValue →
      resumed.registers 14 = fieldLimit →
      resumed.registers 16 = width →
      resumed.registers 18 = remaining + 1 →
      resumed.registers 20 = nodeCount →
      resumed.registers 22 = randomnessCode →
      resumed.registers 24 = projectionQueryOffset width (processed + 1) 0 →
      resumed.registers 25 = encodeBitInput address →
      resumed.registers 26 = spine →
      runNPOracleProgram selectiveUniversalOutputsProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputsProgram maximumBits
        (6 + (calleeFuel + (2 + extraFuel))) machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hflat := hrequestBits
  simp only [structuralAddressInput] at hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have haddressBits := natBitLength_pair_right hpairBits
  rw [show 6 + (calleeFuel + (2 + extraFuel)) =
    5 + (calleeFuel + (2 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 22) rfl) hpc]
  rw [if_neg (by rw [hcount]; omega)]
  rw [show 5 + (calleeFuel + (2 + extraFuel)) =
    4 + (calleeFuel + (2 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair randomnessCode (projectionQueryOffset width processed 0))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.jump, hrandomness, hcursor]) htwo]
  rw [show 4 + (calleeFuel + (2 + extraFuel)) =
    3 + (calleeFuel + (2 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair width
        (Nat.pair randomnessCode (projectionQueryOffset width processed 0)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hone]
  rw [show 3 + (calleeFuel + (2 + extraFuel)) =
    2 + (calleeFuel + (2 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      structuralAddressInput table width randomnessCode
        (projectionQueryOffset width processed 0))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 25) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, htable,
        structuralAddressInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (2 + extraFuel)) =
    1 + (calleeFuel + (2 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 26) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + (calleeFuel + (2 + extraFuel)) =
    calleeFuel + (2 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 27) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := structuralAddressProgram)
    (calleeOutput := encodeBitInput address)
    selectiveUniversalOutputsProgram_addressCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hpairBits
  · intro haltState
    rw [show (2 : ℕ) + extraFuel = 1 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction (value := encodeBitInput address)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 28) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) haddressBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_add_instruction
      (value := projectionQueryOffset width (processed + 1) 0)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 29) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hcursor,
          hwidth, projectionQueryOffset]
        ring)
      hcursorBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump, relocateState,
        hstateRemaining]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hnext]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hselected]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, htable]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, harity]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hrowWidth]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hwidth]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hcount]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hnodeCount]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hrandomness]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine]

set_option maxHeartbeats 1600000 in
-- Ten request steps around the relocated output compiler, then seven unpacking
-- steps and five steps threading the spine and the countdown.
private theorem run_selectiveUniversalOutputsOutputCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (address : BitInput width) (values : List ℕ)
    (table remaining nodeCount randomnessCode processed : ℕ)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveUniversalOutputInput (selectiveStateCode state)
          (descriptionWidth width bound) (rowWidth width bound)
          (boundedCircuitFieldLimit width bound) width nodeCount
          (encodeBitInput address) →
      runNPOracleProgram selectiveUniversalOutputProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalOutputInput (selectiveStateCode state)
            (descriptionWidth width bound) (rowWidth width bound)
            (boundedCircuitFieldLimit width bound) width nodeCount
            (encodeBitInput address)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hnextSpineBits :
      natBitLength (encodeTaggedList (result.output :: values.reverse)) ≤
        maximumBits)
    (hcountBits : natBitLength remaining ≤ maximumBits)
    (hpc : machine.pc = 30)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (htable : machine.registers 8 = table)
    (harity : machine.registers 10 = descriptionWidth width bound)
    (hrowWidth : machine.registers 12 = rowWidth width bound)
    (hfieldLimit :
      machine.registers 14 = boundedCircuitFieldLimit width bound)
    (hwidth : machine.registers 16 = width)
    (hcount : machine.registers 18 = remaining + 1)
    (hnodeCount : machine.registers 20 = nodeCount)
    (hrandomness : machine.registers 22 = randomnessCode)
    (hcursor :
      machine.registers 24 = projectionQueryOffset width (processed + 1) 0)
    (haddress : machine.registers 25 = encodeBitInput address)
    (hspine : machine.registers 26 = encodeTaggedList values.reverse)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 22 →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 8 = table →
      resumed.registers 10 = descriptionWidth width bound →
      resumed.registers 12 = rowWidth width bound →
      resumed.registers 14 = boundedCircuitFieldLimit width bound →
      resumed.registers 16 = width →
      resumed.registers 18 = remaining →
      resumed.registers 20 = nodeCount →
      resumed.registers 22 = randomnessCode →
      resumed.registers 24 = projectionQueryOffset width (processed + 1) 0 →
      resumed.registers 26 =
        encodeTaggedList (result.output :: values.reverse) →
      runNPOracleProgram selectiveUniversalOutputsProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputsProgram maximumBits
        (10 + (calleeFuel + (12 + extraFuel))) machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hwireForm :
      selectiveWireCode result =
        Nat.pair (selectiveStateCode result.state) result.output := rfl
  have hresultForm :
      selectiveStateCode result.state =
        Nat.pair (result.state.target - result.state.next)
          (Nat.pair result.state.next
            (selectiveSelectedCode result.state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveUniversalOutputInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hfive := natBitLength_pair_right hfour
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  rw [hwireForm] at hwireParts
  have hresultStateBits := natBitLength_pair_left hwireParts
  have houtputBits := natBitLength_pair_right hwireParts
  have hresultFlat := hresultStateBits
  rw [hresultForm] at hresultFlat
  have hresultRemainingBits := natBitLength_pair_left hresultFlat
  have hresultTailBits := natBitLength_pair_right hresultFlat
  have hresultNextBits := natBitLength_pair_left hresultTailBits
  have hresultSelectedBits := natBitLength_pair_right hresultTailBits
  have hnextSpineFlat := hnextSpineBits
  simp only [encodeTaggedList] at hnextSpineFlat
  have hconsBits := natBitLength_pair_right hnextSpineFlat
  rw [show 10 + (calleeFuel + (12 + extraFuel)) =
    9 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair nodeCount (encodeBitInput address))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 30) rfl) hpc
    (by rw [hnodeCount, haddress]) hfive]
  rw [show 9 + (calleeFuel + (12 + extraFuel)) =
    8 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair width (Nat.pair nodeCount (encodeBitInput address)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 31) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfour]
  rw [show 8 + (calleeFuel + (12 + extraFuel)) =
    7 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound)
        (Nat.pair width (Nat.pair nodeCount (encodeBitInput address))))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 32) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hthree]
  rw [show 7 + (calleeFuel + (12 + extraFuel)) =
    6 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (rowWidth width bound)
        (Nat.pair (boundedCircuitFieldLimit width bound)
          (Nat.pair width (Nat.pair nodeCount (encodeBitInput address)))))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 33) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowWidth]) htwo]
  rw [show 6 + (calleeFuel + (12 + extraFuel)) =
    5 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair (rowWidth width bound)
          (Nat.pair (boundedCircuitFieldLimit width bound)
            (Nat.pair width (Nat.pair nodeCount (encodeBitInput address))))))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 34) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [show 5 + (calleeFuel + (12 + extraFuel)) =
    4 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 35) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [show 4 + (calleeFuel + (12 + extraFuel)) =
    3 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 36) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateRemaining,
        hstateForm])
    hstateBits]
  rw [show 3 + (calleeFuel + (12 + extraFuel)) =
    2 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveUniversalOutputInput (selectiveStateCode state)
        (descriptionWidth width bound) (rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width nodeCount
        (encodeBitInput address))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 37) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        selectiveUniversalOutputInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (12 + extraFuel)) =
    1 + (calleeFuel + (12 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 38) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + (calleeFuel + (12 + extraFuel)) =
    calleeFuel + (12 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 39) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveUniversalOutputProgram)
    (calleeOutput := selectiveWireCode result)
    selectiveUniversalOutputsProgram_outputCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    rw [show (12 : ℕ) + extraFuel = 11 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode result)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 40) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show (11 : ℕ) + extraFuel = 10 + extraFuel + 1 by omega]
    rw [run_unpairLeft_instruction (value := selectiveStateCode result.state)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 41) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      hresultStateBits]
    rw [show (10 : ℕ) + extraFuel = 9 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction (value := result.output)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 42) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      houtputBits]
    rw [show (9 : ℕ) + extraFuel = 8 + extraFuel + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := result.state.target - result.state.next)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 43) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hresultForm])
      hresultRemainingBits]
    rw [show (8 : ℕ) + extraFuel = 7 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair result.state.next
          (selectiveSelectedCode result.state.selected))
      (selectiveUniversalOutputsProgram_controllerAt (pc := 44) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hresultForm])
      hresultTailBits]
    rw [show (7 : ℕ) + extraFuel = 6 + extraFuel + 1 by omega]
    rw [run_unpairLeft_instruction (value := result.state.next)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 45) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hresultNextBits]
    rw [show (6 : ℕ) + extraFuel = 5 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode result.state.selected)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 46) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hresultSelectedBits]
    rw [show (5 : ℕ) + extraFuel = 4 + extraFuel + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair result.output (encodeTaggedList values.reverse))
      (selectiveUniversalOutputsProgram_controllerAt (pc := 47) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine])
      hconsBits]
    rw [show (4 : ℕ) + extraFuel = 3 + extraFuel + 1 by omega]
    rw [run_set_instruction
      (selectiveUniversalOutputsProgram_controllerAt (pc := 48) rfl) rfl
      (hsmall 1 (by omega))]
    rw [show (3 : ℕ) + extraFuel = 2 + extraFuel + 1 by omega]
    rw [run_pair_instruction
      (value := encodeTaggedList (result.output :: values.reverse))
      (selectiveUniversalOutputsProgram_controllerAt (pc := 49) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, encodeTaggedList])
      hnextSpineBits]
    rw [show (2 : ℕ) + extraFuel = 1 + extraFuel + 1 by omega]
    rw [run_decrement_instruction (value := remaining)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 50) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hcount])
      hcountBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUniversalOutputsProgram_controllerAt (pc := 51) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, htable]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, harity]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hrowWidth]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hwidth]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hnodeCount]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hrandomness]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hcursor]
    · simp [NPOracleState.write, NPOracleState.jump]

-- Three steps around the relocated reverse pass, then five steps building the
-- returned wire list.
private theorem run_selectiveUniversalOutputsExitCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (values : List ℕ) (maximumBits reverseFuel : ℕ) (machine : NPOracleState)
    (hreverseFuel : reverseFuel = structuralTaggedReverseFuel values.reverse)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hreverseBits : structuralTaggedReverseBits values.reverse ≤ maximumBits)
    (hpairBits :
      natBitLength (Nat.pair 0 (encodeTaggedList values)) ≤ maximumBits)
    (houtputBits :
      natBitLength
          (Nat.pair (selectiveStateCode state) (encodeTaggedList values)) ≤
        maximumBits)
    (hpc : machine.pc = 22)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hcount : machine.registers 18 = 0)
    (hspine : machine.registers 26 = encodeTaggedList values.reverse) :
    runNPOracleProgram selectiveUniversalOutputsProgram maximumBits
        (4 + (reverseFuel + 5)) machine =
      some (Nat.pair (selectiveStateCode state) (encodeTaggedList values)) := by
  subst hreverseFuel
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hspineBits :
      natBitLength (encodeTaggedList values.reverse) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (encodeTaggedList values.reverse)
        (encodeTaggedList values.reverse.reverse))).trans hreverseBits
  have hforwardBits :
      natBitLength (encodeTaggedList values) ≤ maximumBits :=
    natBitLength_pair_right hpairBits
  have hstateBits := natBitLength_pair_left houtputBits
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  rw [show 4 + (structuralTaggedReverseFuel values.reverse + 5) =
    3 + (structuralTaggedReverseFuel values.reverse + 5) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 22) rfl) hpc]
  rw [if_pos hcount]
  rw [show 3 + (structuralTaggedReverseFuel values.reverse + 5) =
    2 + (structuralTaggedReverseFuel values.reverse + 5) + 1 by omega]
  rw [run_copy_instruction (value := encodeTaggedList values.reverse)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 52) rfl) rfl
    (by simp [NPOracleState.jump, hspine]) hspineBits]
  rw [show 2 + (structuralTaggedReverseFuel values.reverse + 5) =
    1 + (structuralTaggedReverseFuel values.reverse + 5) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 53) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + (structuralTaggedReverseFuel values.reverse + 5) =
    structuralTaggedReverseFuel values.reverse + 5 + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 54) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := structuralTaggedReverseProgram)
    (calleeOutput := encodeTaggedList values)
    selectiveUniversalOutputsProgram_reverseCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    have hrun :=
      run_structuralTaggedReverseProgram_anyEntry values.reverse frame hframePc
        (by
          rw [hframeInput]
          simp [NPOracleState.write, NPOracleState.jump])
    simpa using run_bits_mono hrun hreverseBits
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hpairBits
  · intro haltState
    rw [show (5 : ℕ) = 4 + 1 by omega]
    rw [run_unpairRight_instruction (value := encodeTaggedList values)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hforwardBits]
    rw [show (4 : ℕ) = 3 + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair state.next (selectiveSelectedCode state.selected))
      (selectiveUniversalOutputsProgram_controllerAt (pc := 56) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hnext,
          hselected])
      hnextSelectedBits]
    rw [show (3 : ℕ) = 2 + 1 by omega]
    rw [run_pair_instruction (value := selectiveStateCode state)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 57) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hstateRemaining, hstateForm])
      hstateBits]
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (selectiveStateCode state) (encodeTaggedList values))
      (selectiveUniversalOutputsProgram_controllerAt (pc := 58) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits]
    exact run_halt_instruction (fuel := 0)
      (selectiveUniversalOutputsProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-! ## 4. The loop

Interpreter resources on this level are data dependent, so the loop's clock and
its register-width envelope are defined by the same recursion as its output. -/

/-- Interpreter fuel of the controller from the loop head. -/
private def universalOutputsLoopFuel {width bound : ℕ} (outputs : List ℕ)
    (outputRunner : SelectiveUniversalOutputRunner width bound)
    (addressRunner : StructuralAddressRunner outputs width)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    SelectiveState (descriptionWidth width bound) → List ℕ → ℕ →
      List (BitInput width) → ℕ
  | _, values, _, [] => 4 + (structuralTaggedReverseFuel values.reverse + 5)
  | state, values, processed, address :: rest =>
      6 +
        (addressRunner.fuel processed randomnessCode +
          (2 +
            (10 +
              (outputRunner.fuel state address nodeCount hnodeCount +
                (12 +
                  universalOutputsLoopFuel outputs outputRunner addressRunner
                    nodeCount hnodeCount randomnessCode
                    (selectiveCompileUniversalOutput state address nodeCount
                      hnodeCount).state
                    (values ++
                      [(selectiveCompileUniversalOutput state address nodeCount
                        hnodeCount).output]) (processed + 1) rest)))))

/-- Register width of the controller from the loop head. -/
private def universalOutputsLoopBits {width bound : ℕ} (outputs : List ℕ)
    (outputRunner : SelectiveUniversalOutputRunner width bound)
    (addressRunner : StructuralAddressRunner outputs width)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    SelectiveState (descriptionWidth width bound) → List ℕ → ℕ →
      List (BitInput width) → ℕ
  | state, values, _, [] =>
      max (structuralTaggedReverseBits values.reverse) <|
        max (natBitLength (Nat.pair 0 (encodeTaggedList values))) <|
          natBitLength
            (Nat.pair (selectiveStateCode state) (encodeTaggedList values))
  | state, values, processed, address :: rest =>
      max
        (natBitLength
          (structuralAddressInput (encodeTaggedList outputs) width
            randomnessCode (projectionQueryOffset width processed 0))) <|
        max (addressRunner.bits processed randomnessCode) <|
          max (natBitLength (Nat.pair 0 (encodeBitInput address))) <|
            max
              (natBitLength
                (projectionQueryOffset width (processed + 1) 0)) <|
              max
                (natBitLength
                  (selectiveUniversalOutputInput (selectiveStateCode state)
                    (descriptionWidth width bound) (rowWidth width bound)
                    (boundedCircuitFieldLimit width bound) width nodeCount
                    (encodeBitInput address))) <|
                max
                  (outputRunner.bits state address nodeCount hnodeCount) <|
                  max
                    (natBitLength
                      (Nat.pair 0
                        (selectiveWireCode
                          (selectiveCompileUniversalOutput state address
                            nodeCount hnodeCount)))) <|
                    max
                      (natBitLength
                        (encodeTaggedList
                          ((selectiveCompileUniversalOutput state address
                            nodeCount hnodeCount).output :: values.reverse))) <|
                      max (natBitLength rest.length) <|
                        universalOutputsLoopBits outputs outputRunner
                          addressRunner nodeCount hnodeCount randomnessCode
                          (selectiveCompileUniversalOutput state address
                            nodeCount hnodeCount).state
                          (values ++
                            [(selectiveCompileUniversalOutput state address
                              nodeCount hnodeCount).output]) (processed + 1)
                          rest

set_option maxHeartbeats 1600000 in
-- The loop is one induction on the remaining queries; each step is discharged
-- by §3's two call frames, and the exit by the third.
private theorem run_selectiveUniversalOutputsLoop {width bound : ℕ}
    (outputs : List ℕ)
    (outputRunner : SelectiveUniversalOutputRunner width bound)
    (addressRunner : StructuralAddressRunner outputs width)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ)
    (maximumBits : ℕ) (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (addresses : List (BitInput width)) (processed : ℕ)
      (state : SelectiveState (descriptionWidth width bound))
      (values : List ℕ) (machine : NPOracleState),
      SelectiveQueriesFrom outputs width randomnessCode processed addresses →
      selectiveStateOrdered state →
      universalOutputsLoopBits outputs outputRunner addressRunner nodeCount
          hnodeCount randomnessCode state values processed addresses ≤
        maximumBits →
      machine.pc = 22 →
      machine.registers 4 = state.target - state.next →
      machine.registers 6 = state.next →
      machine.registers 7 = selectiveSelectedCode state.selected →
      machine.registers 8 = encodeTaggedList outputs →
      machine.registers 10 = descriptionWidth width bound →
      machine.registers 12 = rowWidth width bound →
      machine.registers 14 = boundedCircuitFieldLimit width bound →
      machine.registers 16 = width →
      machine.registers 18 = addresses.length →
      machine.registers 20 = nodeCount →
      machine.registers 22 = randomnessCode →
      machine.registers 24 = projectionQueryOffset width processed 0 →
      machine.registers 26 = encodeTaggedList values.reverse →
      runNPOracleProgram selectiveUniversalOutputsProgram maximumBits
          (universalOutputsLoopFuel outputs outputRunner addressRunner nodeCount
            hnodeCount randomnessCode state values processed addresses)
          machine =
        some
          (universalOutputsOutput nodeCount hnodeCount state values
            addresses) := by
  intro addresses
  induction addresses with
  | nil =>
      intro processed state values machine _ _ hbits hpc hstateRemaining hnext
        hselected _ _ _ _ _ hcount _ _ _ hspine
      simp only [universalOutputsLoopBits] at hbits
      have hreverseBits := (Nat.le_max_left _ _).trans hbits
      have htail0 := (Nat.le_max_right _ _).trans hbits
      have hpairBits := (Nat.le_max_left _ _).trans htail0
      have houtputBits := (Nat.le_max_right _ _).trans htail0
      rw [universalOutputsOutput_nil]
      simp only [universalOutputsLoopFuel]
      exact run_selectiveUniversalOutputsExitCall state values maximumBits _
        machine rfl hsevenBits hreverseBits hpairBits houtputBits hpc
        hstateRemaining hnext hselected (by simpa using hcount) hspine
  | cons address rest inductionHypothesis =>
      intro processed state values machine hqueries hordered hbits hpc
        hstateRemaining hnext hselected htable harity hrowWidth hfieldLimit
        hwidth hcount hnodeCountReg hrandomness hcursor hspine
      simp only [universalOutputsLoopBits] at hbits
      have hrequestBits := (Nat.le_max_left _ _).trans hbits
      have htail0 := (Nat.le_max_right _ _).trans hbits
      have haddressCalleeBits := (Nat.le_max_left _ _).trans htail0
      have htail1 := (Nat.le_max_right _ _).trans htail0
      have haddressPairBits := (Nat.le_max_left _ _).trans htail1
      have htail2 := (Nat.le_max_right _ _).trans htail1
      have hcursorBits := (Nat.le_max_left _ _).trans htail2
      have htail3 := (Nat.le_max_right _ _).trans htail2
      have houtputRequestBits := (Nat.le_max_left _ _).trans htail3
      have htail4 := (Nat.le_max_right _ _).trans htail3
      have houtputCalleeBits := (Nat.le_max_left _ _).trans htail4
      have htail5 := (Nat.le_max_right _ _).trans htail4
      have hwireBits := (Nat.le_max_left _ _).trans htail5
      have htail6 := (Nat.le_max_right _ _).trans htail5
      have hnextSpineBits := (Nat.le_max_left _ _).trans htail6
      have htail7 := (Nat.le_max_right _ _).trans htail6
      have hcountBits := (Nat.le_max_left _ _).trans htail7
      have hrecursiveBits := (Nat.le_max_right _ _).trans htail7
      have haddressValue :
          address =
            projectionTableAddress outputs width processed
              (tableRandomness width randomnessCode) := hqueries.1
      rw [universalOutputsOutput_cons]
      simp only [universalOutputsLoopFuel]
      refine run_selectiveUniversalOutputsAddressCall address
        (encodeTaggedList outputs) (descriptionWidth width bound)
        (rowWidth width bound) (boundedCircuitFieldLimit width bound)
        (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) rest.length nodeCount
        randomnessCode processed (encodeTaggedList values.reverse) maximumBits
        _ _ _ machine ?_ hsevenBits hrequestBits haddressPairBits hcursorBits
        hpc hstateRemaining hnext hselected htable harity hrowWidth hfieldLimit
        hwidth (by simpa using hcount) hnodeCountReg hrandomness hcursor hspine
        ?_
      · intro frame hframePc hframeInput
        rw [haddressValue]
        exact run_bits_mono
          (addressRunner.executes processed randomnessCode frame hframePc
            hframeInput) haddressCalleeBits
      intro middle hmiddlePc hmiddleRemaining hmiddleNext hmiddleSelected
        hmiddleTable hmiddleArity hmiddleRowWidth hmiddleFieldLimit
        hmiddleWidth hmiddleCount hmiddleNodeCount hmiddleRandomness
        hmiddleCursor hmiddleAddress hmiddleSpine
      refine run_selectiveUniversalOutputsOutputCall state
        (selectiveCompileUniversalOutput state address nodeCount hnodeCount)
        address values (encodeTaggedList outputs) rest.length nodeCount
        randomnessCode processed maximumBits _ _ _ middle ?_ hsevenBits
        houtputRequestBits hwireBits hnextSpineBits hcountBits hmiddlePc
        hmiddleRemaining hmiddleNext hmiddleSelected hmiddleTable hmiddleArity
        hmiddleRowWidth hmiddleFieldLimit hmiddleWidth hmiddleCount
        hmiddleNodeCount hmiddleRandomness hmiddleCursor hmiddleAddress
        hmiddleSpine ?_
      · intro frame hframePc hframeInput
        exact run_bits_mono
          (outputRunner.executes state address nodeCount hnodeCount hordered
            frame hframePc hframeInput) houtputCalleeBits
      · intro final hfinalPc hfinalRemaining hfinalNext hfinalSelected
          hfinalTable hfinalArity hfinalRowWidth hfinalFieldLimit hfinalWidth
          hfinalCount hfinalNodeCount hfinalRandomness hfinalCursor hfinalSpine
        refine inductionHypothesis (processed + 1)
          (selectiveCompileUniversalOutput state address nodeCount
            hnodeCount).state
          (values ++
            [(selectiveCompileUniversalOutput state address nodeCount
              hnodeCount).output]) final hqueries.2
          (selectiveCompileUniversalOutput_ordered state address nodeCount
            hnodeCount hordered)
          hrecursiveBits hfinalPc hfinalRemaining hfinalNext hfinalSelected
          hfinalTable hfinalArity hfinalRowWidth hfinalFieldLimit hfinalWidth
          (by simpa using hfinalCount) hfinalNodeCount hfinalRandomness
          hfinalCursor ?_
        rw [hfinalSpine]
        simp

/-! ## 5. The request parser and the level runner

§4's loop consumes two callee runs: the output compiler of
`SelectiveUniversalOutputRun` and the address evaluator of
`SelectiveClauseRun`.  §5 feeds the loop from the twenty-two-step request
parser and packages the whole level in the runner shape the caller one level up
consumes. -/

set_option maxHeartbeats 1600000 in
-- Twenty unpair steps and two zeroing steps set up the loop's registers.
private theorem run_selectiveUniversalOutputsPrologue {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (table count nodeCount randomnessCode : ℕ)
    (maximumBits loopFuel finalOutput : ℕ) (entry : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalOutputsInput (selectiveStateCode state) table
            (descriptionWidth width bound) (rowWidth width bound)
            (boundedCircuitFieldLimit width bound) width count nodeCount
            randomnessCode) ≤
        maximumBits)
    (hpc : entry.pc = 0)
    (hinput :
      entry.registers 0 =
        selectiveUniversalOutputsInput (selectiveStateCode state) table
          (descriptionWidth width bound) (rowWidth width bound)
          (boundedCircuitFieldLimit width bound) width count nodeCount
          randomnessCode)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 22 →
      resumed.registers 4 = state.target - state.next →
      resumed.registers 6 = state.next →
      resumed.registers 7 = selectiveSelectedCode state.selected →
      resumed.registers 8 = table →
      resumed.registers 10 = descriptionWidth width bound →
      resumed.registers 12 = rowWidth width bound →
      resumed.registers 14 = boundedCircuitFieldLimit width bound →
      resumed.registers 16 = width →
      resumed.registers 18 = count →
      resumed.registers 20 = nodeCount →
      resumed.registers 22 = randomnessCode →
      resumed.registers 24 = 0 →
      resumed.registers 26 = 0 →
      runNPOracleProgram selectiveUniversalOutputsProgram maximumBits loopFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputsProgram maximumBits
        (22 + loopFuel) entry =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveUniversalOutputsInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htableBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have harityBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hrowWidthBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hfieldLimitBits := natBitLength_pair_left hfour
  have hfive := natBitLength_pair_right hfour
  have hwidthBits := natBitLength_pair_left hfive
  have hsix := natBitLength_pair_right hfive
  have hcountBits := natBitLength_pair_left hsix
  have hseven := natBitLength_pair_right hsix
  have hnodeCountBits := natBitLength_pair_left hseven
  have hrandomnessBits := natBitLength_pair_right hseven
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show 22 + loopFuel = 21 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveUniversalOutputsInput]) hstateBits]
  rw [show 21 + loopFuel = 20 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair table <|
        Nat.pair (descriptionWidth width bound) <|
          Nat.pair (rowWidth width bound) <|
            Nat.pair (boundedCircuitFieldLimit width bound) <|
              Nat.pair width (Nat.pair count (Nat.pair nodeCount
                randomnessCode)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveUniversalOutputsInput])
    hone]
  rw [show 20 + loopFuel = 19 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 19 + loopFuel = 18 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [show 18 + loopFuel = 17 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 17 + loopFuel = 16 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [show 16 + loopFuel = 15 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := table)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htableBits]
  rw [show 15 + loopFuel = 14 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (descriptionWidth width bound) <|
        Nat.pair (rowWidth width bound) <|
          Nat.pair (boundedCircuitFieldLimit width bound) <|
            Nat.pair width (Nat.pair count (Nat.pair nodeCount
              randomnessCode)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [show 14 + loopFuel = 13 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := descriptionWidth width bound)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 13 + loopFuel = 12 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (rowWidth width bound) <|
        Nat.pair (boundedCircuitFieldLimit width bound) <|
          Nat.pair width (Nat.pair count (Nat.pair nodeCount randomnessCode)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 12 + loopFuel = 11 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowWidth width bound)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [show 11 + loopFuel = 10 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound) <|
        Nat.pair width (Nat.pair count (Nat.pair nodeCount randomnessCode)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [show 10 + loopFuel = 9 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := boundedCircuitFieldLimit width bound)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [show 9 + loopFuel = 8 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair count (Nat.pair nodeCount
      randomnessCode)))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [show 8 + loopFuel = 7 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show 7 + loopFuel = 6 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair count (Nat.pair nodeCount randomnessCode))
    (selectiveUniversalOutputsProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsix]
  rw [show 6 + loopFuel = 5 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 16) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [show 5 + loopFuel = 4 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair nodeCount randomnessCode)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 17) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hseven]
  rw [show 4 + loopFuel = 3 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := nodeCount)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodeCountBits]
  rw [show 3 + loopFuel = 2 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction (value := randomnessCode)
    (selectiveUniversalOutputsProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrandomnessBits]
  rw [show 2 + loopFuel = 1 + loopFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 20) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + loopFuel = loopFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputsProgram_controllerAt (pc := 21) rfl) rfl
    (hsmall 0 (by omega))]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]

/-- The projected query list one verifier row compiles. -/
def selectiveProjectedAddresses (outputs : List ℕ)
    (width count randomnessCode : ℕ) : List (BitInput width) :=
  List.ofFn fun query : Fin count =>
    projectionTableAddress outputs width query.val
      (tableRandomness width randomnessCode)

/-- **Level premise.**  The projected query compiler compiles every projected
query of one verifier row at its own ABI frame, at an arbitrary entry state,
and returns the compiler state beside the forward list of query wires. -/
structure SelectiveUniversalOutputsRunner (outputs : List ℕ)
    (width bound : ℕ) where
  /-- Register width of one projected query list compilation. -/
  bits : SelectiveState (descriptionWidth width bound) → ℕ →
    ∀ nodeCount : ℕ, nodeCount ≤ bound → ℕ → ℕ
  /-- Interpreter fuel of one projected query list compilation. -/
  fuel : SelectiveState (descriptionWidth width bound) → ℕ →
    ∀ nodeCount : ℕ, nodeCount ≤ bound → ℕ → ℕ
  /-- The published run, at an arbitrary entry state. -/
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
      (randomnessCode : ℕ), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveUniversalOutputsInput (selectiveStateCode state)
        (encodeTaggedList outputs) (descriptionWidth width bound)
        (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
        count nodeCount randomnessCode →
    runNPOracleProgram selectiveUniversalOutputsProgram
        (bits state count nodeCount hnodeCount randomnessCode)
        (fuel state count nodeCount hnodeCount randomnessCode) entry =
      some
        (selectiveWireListCode
          (selectiveCompileUniversalOutputs state nodeCount hnodeCount
            (selectiveProjectedAddresses outputs width count randomnessCode)))

/-- Register width of one projected query list compilation. -/
def selectiveUniversalOutputsRunBits {width bound : ℕ} (outputs : List ℕ)
    (outputRunner : SelectiveUniversalOutputRunner width bound)
    (addressRunner : StructuralAddressRunner outputs width)
    (state : SelectiveState (descriptionWidth width bound)) (count : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveUniversalOutputsInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount randomnessCode)) <|
      universalOutputsLoopBits outputs outputRunner addressRunner nodeCount
        hnodeCount randomnessCode state [] 0
        (selectiveProjectedAddresses outputs width count randomnessCode)

/-- Interpreter fuel of one projected query list compilation. -/
def selectiveUniversalOutputsRunFuel {width bound : ℕ} (outputs : List ℕ)
    (outputRunner : SelectiveUniversalOutputRunner width bound)
    (addressRunner : StructuralAddressRunner outputs width)
    (state : SelectiveState (descriptionWidth width bound)) (count : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ) :
    ℕ :=
  22 +
    universalOutputsLoopFuel outputs outputRunner addressRunner nodeCount
      hnodeCount randomnessCode state [] 0
      (selectiveProjectedAddresses outputs width count randomnessCode)

/-- **The projected query compiler's run, from the two levels below it.**  The
`1256`-instruction stream compiles exactly the query list the source compiler
produces.  Only the universal-evaluator output compiler and the address
evaluator remain as premises; the tagged reverse pass is consumed opaquely. -/
def selectiveUniversalOutputsRunnerOfLevels {width bound : ℕ}
    (outputs : List ℕ)
    (outputRunner : SelectiveUniversalOutputRunner width bound)
    (addressRunner : StructuralAddressRunner outputs width) :
    SelectiveUniversalOutputsRunner outputs width bound where
  bits := fun state count nodeCount hnodeCount randomnessCode =>
    selectiveUniversalOutputsRunBits outputs outputRunner addressRunner state
      count nodeCount hnodeCount randomnessCode
  fuel := fun state count nodeCount hnodeCount randomnessCode =>
    selectiveUniversalOutputsRunFuel outputs outputRunner addressRunner state
      count nodeCount hnodeCount randomnessCode
  executes := by
    intro state count nodeCount hnodeCount randomnessCode hordered entry
      hentryPc hentryInput
    have hsevenBits :
        natBitLength 7 ≤
          selectiveUniversalOutputsRunBits outputs outputRunner addressRunner
            state count nodeCount hnodeCount randomnessCode :=
      Nat.le_max_left _ _
    have htail0 :
        max
            (natBitLength
              (selectiveUniversalOutputsInput (selectiveStateCode state)
                (encodeTaggedList outputs) (descriptionWidth width bound)
                (rowWidth width bound) (boundedCircuitFieldLimit width bound)
                width count nodeCount randomnessCode))
            (universalOutputsLoopBits outputs outputRunner addressRunner
              nodeCount hnodeCount randomnessCode state [] 0
              (selectiveProjectedAddresses outputs width count
                randomnessCode)) ≤
          selectiveUniversalOutputsRunBits outputs outputRunner addressRunner
            state count nodeCount hnodeCount randomnessCode :=
      Nat.le_max_right _ _
    have hrequestBits := (Nat.le_max_left _ _).trans htail0
    have hloopBits := (Nat.le_max_right _ _).trans htail0
    have houtput :
        selectiveWireListCode
            (selectiveCompileUniversalOutputs state nodeCount hnodeCount
              (selectiveProjectedAddresses outputs width count
                randomnessCode)) =
          universalOutputsOutput nodeCount hnodeCount state []
            (selectiveProjectedAddresses outputs width count
              randomnessCode) := by
      simp only [selectiveWireListCode, universalOutputsOutput, List.nil_append]
    rw [houtput]
    unfold selectiveUniversalOutputsRunFuel
    refine run_selectiveUniversalOutputsPrologue state
      (encodeTaggedList outputs) count nodeCount randomnessCode _ _ _ entry
      hsevenBits hrequestBits hentryPc hentryInput ?_
    intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
      hresumedTable hresumedArity hresumedRowWidth hresumedFieldLimit
      hresumedWidth hresumedCount hresumedNodeCount hresumedRandomness
      hresumedCursor hresumedSpine
    refine run_selectiveUniversalOutputsLoop outputs outputRunner addressRunner
      nodeCount hnodeCount randomnessCode _ hsevenBits
      (selectiveProjectedAddresses outputs width count randomnessCode) 0 state
      [] resumed ?_ hordered hloopBits hresumedPc hresumedRemaining
      hresumedNext hresumedSelected hresumedTable hresumedArity
      hresumedRowWidth hresumedFieldLimit hresumedWidth ?_ hresumedNodeCount
      hresumedRandomness ?_ ?_
    · exact selectiveQueriesFrom_ofFn outputs width randomnessCode count 0
        (fun query => query.val) (by simp)
    · rw [hresumedCount]
      simp [selectiveProjectedAddresses]
    · rw [hresumedCursor]
      simp [projectionQueryOffset]
    · rw [hresumedSpine]
      simp [encodeTaggedList]

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
