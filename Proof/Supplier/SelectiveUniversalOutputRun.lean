import Proof.Supplier.SelectiveUniversalNodeRun
import Proof.Circuits.StructuralTaggedReverseEntry
import Batteries.Tactic.OpenPrivate

/-!
# The universal evaluator's output compiler run

`selectiveUniversalOutputProgram` is the `909`-instruction stream that compiles
every row of one described DAG and then selects the evaluator's output wire.
It is a controller of `61` instructions with three relocated callees: the
`641`-instruction row compiler, the `11`-instruction tagged reverse pass and the
`196`-instruction field selector.

The controller is a loop.  Live row outputs stay on one private reverse spine in
register `19`, and the reverse callee at the loop head materialises the forward
view in register `20` before every consumer — including the exit, which needs
the same forward list for its single output selection.  Each iteration compiles
one row through the relocated row compiler, conses its wire onto the spine,
advances the row cursor in register `18` by one row width and counts register
`16` down.  The exit runs one field selection at the output row.

This module executes that controller.  The reverse pass is consumed opaquely
through its entry-independent run; the row compiler and the field selector are
named runner premises one level down.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
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

open private selectiveUniversalOutputInput
  selectiveUniversalOutputControllerProgram
  selectiveUniversalOutputControllerProgram_length
  selectiveUniversalOutputProgram selectiveUniversalNodeInput
  selectiveUniversalNodeProgram selectiveFieldSelectInput
  selectiveFieldSelectProgram selectiveFieldSelectProgram_length
  structuralTaggedReverseProgram structuralTaggedReverseFuel
  structuralTaggedReverseBits from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

open private selectiveCompileUniversalNode_ordered from
  Proof.Supplier.SelectiveCountCasesRun

/-! ## 1. Decoding the fixed 909-instruction stream

The controller occupies the first `61` positions, the row compiler the next
`641`, the reverse pass the next `11` and the field selector the last `196`.
Every later step decodes through exactly one of the four lemmas below. -/

set_option maxRecDepth 20000 in
private theorem selectiveUniversalNodeProgram_length_eq :
    selectiveUniversalNodeProgram.length = 641 := by
  rfl

private theorem structuralTaggedReverseProgram_length_eq :
    structuralTaggedReverseProgram.length = 11 := by
  rfl

private theorem jump_registers_eq (state : NPOracleState) (target index : ℕ) :
    (state.jump target).registers index = state.registers index :=
  rfl

private theorem selectiveUniversalOutputProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveUniversalOutputControllerProgram 61 702 713)[pc]? =
        some instruction) :
    selectiveUniversalOutputProgram[pc]? = some instruction := by
  have hpc :
      pc < (selectiveUniversalOutputControllerProgram 61 702 713).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUniversalOutputControllerProgram_length] at hpc
  simp only [selectiveUniversalOutputProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq,
      structuralTaggedReverseProgram_length_eq]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveUniversalOutputControllerProgram_length]
    omega)]
  exact hlookup

private theorem selectiveUniversalOutputProgram_nodeCallable :
    ProgramCallableAt selectiveUniversalOutputProgram
      selectiveUniversalNodeProgram 61 1000 50 36 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUniversalNodeProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUniversalNodeProgram_length_eq] at hpc
  simp only [selectiveUniversalOutputProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq,
      structuralTaggedReverseProgram_length_eq]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveUniversalOutputControllerProgram_length]
    omega)]
  simp only [selectiveUniversalOutputControllerProgram_length]
  rw [show 61 + pc - 61 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveUniversalOutputProgram_reverseCallable :
    ProgramCallableAt selectiveUniversalOutputProgram
      structuralTaggedReverseProgram 702 12000 50 24 := by
  intro pc instruction hlookup
  have hpc : pc < structuralTaggedReverseProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [structuralTaggedReverseProgram_length_eq] at hpc
  simp only [selectiveUniversalOutputProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq,
      structuralTaggedReverseProgram_length_eq]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalOutputControllerProgram_length,
    selectiveUniversalNodeProgram_length_eq]
  rw [show 702 + pc - (61 + 641) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveUniversalOutputProgram_fieldCallable :
    ProgramCallableAt selectiveUniversalOutputProgram
      selectiveFieldSelectProgram 713 13000 50 59 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveFieldSelectProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveFieldSelectProgram_length] at hpc
  simp only [selectiveUniversalOutputProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalOutputControllerProgram_length,
      selectiveUniversalNodeProgram_length_eq,
      structuralTaggedReverseProgram_length_eq]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalOutputControllerProgram_length,
    selectiveUniversalNodeProgram_length_eq,
    structuralTaggedReverseProgram_length_eq]
  rw [show 713 + pc - (61 + 641 + 11) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 2. The controller's loop, at the typed level

The source compiler builds the row list by recursion from the last row down,
while the controller compiles rows in ascending order from a moving cursor.  §2
names the ascending recursion and identifies the two. -/

private theorem universalOutputFieldBlock (width bound : ℕ) :
    6 + boundedCircuitFieldLimit width bound ≤ rowWidth width bound := by
  change 6 + boundedCircuitFieldLimit width bound ≤
    6 + 2 * boundedCircuitFieldLimit width bound
  omega

/-- The rows the controller still has to compile, in the ascending order it
visits them. -/
private def universalOutputNodes {width bound : ℕ} (address : BitInput width) :
    (remaining processed : ℕ) → processed + remaining ≤ bound →
      SelectiveState (descriptionWidth width bound) → List ℕ →
      SelectiveWireList (descriptionWidth width bound)
  | 0, _, _, state, values => { state, values }
  | remaining + 1, processed, hbound, state, values =>
      universalOutputNodes address remaining (processed + 1) (by omega)
        (selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
          values).state
        (values ++
          [(selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
            values).output])

/-- The compiler wire the controller produces from the loop head. -/
private def universalOutputWire {width bound : ℕ} (address : BitInput width)
    (outputRow : Fin (bound + 1)) (remaining processed : ℕ)
    (hbound : processed + remaining ≤ bound)
    (state : SelectiveState (descriptionWidth width bound)) (values : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileFirstFieldSelect
    (universalOutputNodes address remaining processed hbound state values).state
    outputRow
    (universalOutputNodes address remaining processed hbound state values).values

private theorem universalOutputWire_succ {width bound : ℕ}
    (address : BitInput width) (outputRow : Fin (bound + 1))
    (remaining processed : ℕ) (hbound : processed + (remaining + 1) ≤ bound)
    (state : SelectiveState (descriptionWidth width bound))
    (values : List ℕ) :
    universalOutputWire address outputRow (remaining + 1) processed hbound state
        values =
      universalOutputWire address outputRow remaining (processed + 1)
        (by omega)
        (selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
          values).state
        (values ++
          [(selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
            values).output]) := by
  simp only [universalOutputWire, universalOutputNodes]

/-- **The controller's scheduling identity.**  Compiling the rows in ascending
order from the empty prefix is exactly the source compiler's descending
recursion. -/
private theorem universalOutputNodes_eq {width bound : ℕ}
    (address : BitInput width)
    (state : SelectiveState (descriptionWidth width bound)) :
    ∀ (remaining processed total : ℕ) (hbound : processed + remaining ≤ bound)
      (hprocessed : processed ≤ bound) (htotal : total ≤ bound),
      processed + remaining = total →
      universalOutputNodes address remaining processed hbound
          (selectiveCompileUniversalNodes state address processed
            hprocessed).state
          (selectiveCompileUniversalNodes state address processed
            hprocessed).values =
        selectiveCompileUniversalNodes state address total htotal := by
  intro remaining
  induction remaining with
  | zero =>
      intro processed total hbound hprocessed htotal hsum
      subst hsum
      rfl
  | succ remaining inductionHypothesis =>
      intro processed total hbound hprocessed htotal hsum
      rw [universalOutputNodes]
      exact inductionHypothesis (processed + 1) total (by omega) (by omega)
        htotal (by omega)

-- Three request steps around the relocated reverse pass, then one unpacking
-- step; the branch register at the call site is never decided.
private theorem run_selectiveUniversalOutputReverseCall (values : List ℕ)
    (maximumBits reverseFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hreverseFuel : reverseFuel = structuralTaggedReverseFuel values.reverse)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hreverseBits : structuralTaggedReverseBits values.reverse ≤ maximumBits)
    (hpairBits :
      natBitLength (Nat.pair 0 (encodeTaggedList values)) ≤ maximumBits)
    (hpc : machine.pc = 21)
    (hspine : machine.registers 19 = encodeTaggedList values.reverse)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 25 →
      resumed.registers 20 = encodeTaggedList values →
      (∀ index : ℕ, index < 12000 ∧ index ≠ 20 ∧ index ≠ 50 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalOutputProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputProgram maximumBits
        (3 + (reverseFuel + (1 + extraFuel))) machine =
      some finalOutput := by
  subst hreverseFuel
  have hspineBits :
      natBitLength (encodeTaggedList values.reverse) ≤ maximumBits :=
    (natBitLength_mono
      (Nat.left_le_pair (encodeTaggedList values.reverse)
        (encodeTaggedList values.reverse.reverse))).trans hreverseBits
  have hforwardBits :
      natBitLength (encodeTaggedList values) ≤ maximumBits :=
    natBitLength_pair_right hpairBits
  rw [show 3 + (structuralTaggedReverseFuel values.reverse + (1 + extraFuel)) =
    2 + (structuralTaggedReverseFuel values.reverse + (1 + extraFuel)) + 1 by
    omega]
  rw [run_copy_instruction (value := encodeTaggedList values.reverse)
    (selectiveUniversalOutputProgram_controllerAt (pc := 21) rfl) hpc hspine
    hspineBits]
  rw [show 2 + (structuralTaggedReverseFuel values.reverse + (1 + extraFuel)) =
    1 + (structuralTaggedReverseFuel values.reverse + (1 + extraFuel)) + 1 by
    omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 22) rfl) rfl hzeroBits]
  rw [show 1 + (structuralTaggedReverseFuel values.reverse + (1 + extraFuel)) =
    structuralTaggedReverseFuel values.reverse + (1 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 23) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := structuralTaggedReverseProgram)
    (calleeOutput := encodeTaggedList values)
    selectiveUniversalOutputProgram_reverseCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction (value := encodeTaggedList values)
      (selectiveUniversalOutputProgram_controllerAt (pc := 24) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hforwardBits]
    refine hcontinue _ rfl ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · intro index hindex
      obtain ⟨hlow, h20, h50⟩ := hindex
      have hframe : ¬ (12000 ≤ index) := by omega
      have hcell : index ≠ 12000 := by omega
      simp [NPOracleState.write, NPOracleState.jump, relocateState, hframe,
        hcell, h20, h50]

set_option maxHeartbeats 1600000 in
-- Ten request steps around the relocated row compiler, then seven unpacking
-- steps and six steps threading the spine, the row cursor and the countdown.
private theorem run_selectiveUniversalOutputNodeCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (address : BitInput width) (values : List ℕ) (remaining processed : ℕ)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveUniversalNodeInput (selectiveStateCode state)
          (descriptionWidth width bound) (processed * rowWidth width bound)
          (boundedCircuitFieldLimit width bound) width (encodeBitInput address)
          (encodeTaggedList values) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalNodeInput (selectiveStateCode state)
            (descriptionWidth width bound) (processed * rowWidth width bound)
            (boundedCircuitFieldLimit width bound) width
            (encodeBitInput address) (encodeTaggedList values)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hnextSpineBits :
      natBitLength (encodeTaggedList (result.output :: values.reverse)) ≤
        maximumBits)
    (hcursorBits :
      natBitLength
          (processed * rowWidth width bound + rowWidth width bound) ≤
        maximumBits)
    (hcountBits : natBitLength remaining ≤ maximumBits)
    (hpc : machine.pc = 26)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hrowWidth : machine.registers 10 = rowWidth width bound)
    (hfieldLimit :
      machine.registers 12 = boundedCircuitFieldLimit width bound)
    (hwidth : machine.registers 14 = width)
    (hcount : machine.registers 16 = remaining + 1)
    (haddress : machine.registers 17 = encodeBitInput address)
    (hcursor : machine.registers 18 = processed * rowWidth width bound)
    (hspine : machine.registers 19 = encodeTaggedList values.reverse)
    (hforward : machine.registers 20 = encodeTaggedList values)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 8 = descriptionWidth width bound →
      resumed.registers 10 = rowWidth width bound →
      resumed.registers 12 = boundedCircuitFieldLimit width bound →
      resumed.registers 14 = width →
      resumed.registers 16 = remaining →
      resumed.registers 17 = encodeBitInput address →
      resumed.registers 18 =
        processed * rowWidth width bound + rowWidth width bound →
      resumed.registers 19 =
        encodeTaggedList (result.output :: values.reverse) →
      runNPOracleProgram selectiveUniversalOutputProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputProgram maximumBits
        (10 + (calleeFuel + (13 + extraFuel))) machine =
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
  simp only [selectiveUniversalNodeInput] at hflat
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
  rw [show 10 + (calleeFuel + (13 + extraFuel)) =
    9 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalOutputProgram_controllerAt (pc := 26) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 9 + (calleeFuel + (13 + extraFuel)) =
    8 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalOutputProgram_controllerAt (pc := 27) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateRemaining,
        hstateForm])
    hstateBits]
  rw [show 8 + (calleeFuel + (13 + extraFuel)) =
    7 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair (encodeBitInput address) (encodeTaggedList values))
    (selectiveUniversalOutputProgram_controllerAt (pc := 28) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, haddress, hforward])
    hfive]
  rw [show 7 + (calleeFuel + (13 + extraFuel)) =
    6 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair width
        (Nat.pair (encodeBitInput address) (encodeTaggedList values)))
    (selectiveUniversalOutputProgram_controllerAt (pc := 29) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfour]
  rw [show 6 + (calleeFuel + (13 + extraFuel)) =
    5 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound)
        (Nat.pair width
          (Nat.pair (encodeBitInput address) (encodeTaggedList values))))
    (selectiveUniversalOutputProgram_controllerAt (pc := 30) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hthree]
  rw [show 5 + (calleeFuel + (13 + extraFuel)) =
    4 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (processed * rowWidth width bound)
        (Nat.pair (boundedCircuitFieldLimit width bound)
          (Nat.pair width
            (Nat.pair (encodeBitInput address) (encodeTaggedList values)))))
    (selectiveUniversalOutputProgram_controllerAt (pc := 31) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcursor]) htwo]
  rw [show 4 + (calleeFuel + (13 + extraFuel)) =
    3 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair (processed * rowWidth width bound)
          (Nat.pair (boundedCircuitFieldLimit width bound)
            (Nat.pair width
              (Nat.pair (encodeBitInput address) (encodeTaggedList values))))))
    (selectiveUniversalOutputProgram_controllerAt (pc := 32) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [show 3 + (calleeFuel + (13 + extraFuel)) =
    2 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveUniversalNodeInput (selectiveStateCode state)
        (descriptionWidth width bound) (processed * rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width (encodeBitInput address)
        (encodeTaggedList values))
    (selectiveUniversalOutputProgram_controllerAt (pc := 33) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        selectiveUniversalNodeInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (13 + extraFuel)) =
    1 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 34) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + (calleeFuel + (13 + extraFuel)) =
    calleeFuel + (13 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 35) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveUniversalNodeProgram)
    (calleeOutput := selectiveWireCode result)
    selectiveUniversalOutputProgram_nodeCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    rw [show (13 : ℕ) + extraFuel = 12 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode result)
      (selectiveUniversalOutputProgram_controllerAt (pc := 36) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show (12 : ℕ) + extraFuel = 11 + extraFuel + 1 by omega]
    rw [run_unpairLeft_instruction (value := selectiveStateCode result.state)
      (selectiveUniversalOutputProgram_controllerAt (pc := 37) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      hresultStateBits]
    rw [show (11 : ℕ) + extraFuel = 10 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction (value := result.output)
      (selectiveUniversalOutputProgram_controllerAt (pc := 38) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      houtputBits]
    rw [show (10 : ℕ) + extraFuel = 9 + extraFuel + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := result.state.target - result.state.next)
      (selectiveUniversalOutputProgram_controllerAt (pc := 39) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hresultForm])
      hresultRemainingBits]
    rw [show (9 : ℕ) + extraFuel = 8 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair result.state.next
          (selectiveSelectedCode result.state.selected))
      (selectiveUniversalOutputProgram_controllerAt (pc := 40) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hresultForm])
      hresultTailBits]
    rw [show (8 : ℕ) + extraFuel = 7 + extraFuel + 1 by omega]
    rw [run_unpairLeft_instruction (value := result.state.next)
      (selectiveUniversalOutputProgram_controllerAt (pc := 41) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hresultNextBits]
    rw [show (7 : ℕ) + extraFuel = 6 + extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode result.state.selected)
      (selectiveUniversalOutputProgram_controllerAt (pc := 42) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hresultSelectedBits]
    rw [show (6 : ℕ) + extraFuel = 5 + extraFuel + 1 by omega]
    rw [run_pair_instruction
      (value := Nat.pair result.output (encodeTaggedList values.reverse))
      (selectiveUniversalOutputProgram_controllerAt (pc := 43) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine])
      hconsBits]
    rw [show (5 : ℕ) + extraFuel = 4 + extraFuel + 1 by omega]
    rw [run_set_instruction
      (selectiveUniversalOutputProgram_controllerAt (pc := 44) rfl) rfl
      (hsmall 1 (by omega))]
    rw [show (4 : ℕ) + extraFuel = 3 + extraFuel + 1 by omega]
    rw [run_pair_instruction
      (value := encodeTaggedList (result.output :: values.reverse))
      (selectiveUniversalOutputProgram_controllerAt (pc := 45) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, encodeTaggedList])
      hnextSpineBits]
    rw [show (3 : ℕ) + extraFuel = 2 + extraFuel + 1 by omega]
    rw [run_add_instruction
      (value := processed * rowWidth width bound + rowWidth width bound)
      (selectiveUniversalOutputProgram_controllerAt (pc := 46) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hcursor,
          hrowWidth])
      hcursorBits]
    rw [show (2 : ℕ) + extraFuel = 1 + extraFuel + 1 by omega]
    rw [run_decrement_instruction (value := remaining)
      (selectiveUniversalOutputProgram_controllerAt (pc := 47) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hcount])
      hcountBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUniversalOutputProgram_controllerAt (pc := 48) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, harity]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hrowWidth]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hwidth]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, haddress]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]

set_option maxHeartbeats 1600000 in
-- Ten request steps around the relocated field selector, then two steps
-- returning the evaluator's output wire.
private theorem run_selectiveUniversalOutputFieldCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (values : List ℕ) (processed : ℕ) (maximumBits calleeFuel : ℕ)
    (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode state)
          (descriptionWidth width bound) (processed * rowWidth width bound) 6
          (boundedCircuitFieldLimit width bound) (encodeTaggedList values) →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode state)
            (descriptionWidth width bound) (processed * rowWidth width bound) 6
            (boundedCircuitFieldLimit width bound)
            (encodeTaggedList values)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hpc : machine.pc = 49)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hfieldLimit :
      machine.registers 12 = boundedCircuitFieldLimit width bound)
    (hcursor : machine.registers 18 = processed * rowWidth width bound)
    (hforward : machine.registers 20 = encodeTaggedList values) :
    runNPOracleProgram selectiveUniversalOutputProgram maximumBits
        (10 + (calleeFuel + 2)) machine =
      some (selectiveWireCode result) := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveFieldSelectInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hwireFlat := natBitLength_pair_right hwireBits
  rw [show 10 + (calleeFuel + 2) = 9 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalOutputProgram_controllerAt (pc := 49) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 9 + (calleeFuel + 2) = 8 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalOutputProgram_controllerAt (pc := 50) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateRemaining,
        hstateForm])
    hstateBits]
  rw [show 8 + (calleeFuel + 2) = 7 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound)
        (encodeTaggedList values))
    (selectiveUniversalOutputProgram_controllerAt (pc := 51) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit, hforward])
    hfour]
  rw [show 7 + (calleeFuel + 2) = 6 + (calleeFuel + 2) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 52) rfl) rfl
    (hsmall 6 (by omega))]
  rw [show 6 + (calleeFuel + 2) = 5 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair 6
        (Nat.pair (boundedCircuitFieldLimit width bound)
          (encodeTaggedList values)))
    (selectiveUniversalOutputProgram_controllerAt (pc := 53) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 5 + (calleeFuel + 2) = 4 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (processed * rowWidth width bound)
        (Nat.pair 6
          (Nat.pair (boundedCircuitFieldLimit width bound)
            (encodeTaggedList values))))
    (selectiveUniversalOutputProgram_controllerAt (pc := 54) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcursor]) htwo]
  rw [show 4 + (calleeFuel + 2) = 3 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair (processed * rowWidth width bound)
          (Nat.pair 6
            (Nat.pair (boundedCircuitFieldLimit width bound)
              (encodeTaggedList values)))))
    (selectiveUniversalOutputProgram_controllerAt (pc := 55) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [show 3 + (calleeFuel + 2) = 2 + (calleeFuel + 2) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveFieldSelectInput (selectiveStateCode state)
        (descriptionWidth width bound) (processed * rowWidth width bound) 6
        (boundedCircuitFieldLimit width bound) (encodeTaggedList values))
    (selectiveUniversalOutputProgram_controllerAt (pc := 56) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, selectiveFieldSelectInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + 2) = 1 + (calleeFuel + 2) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 57) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + (calleeFuel + 2) = calleeFuel + 2 + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 58) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveFieldSelectProgram)
    (calleeOutput := selectiveWireCode result)
    selectiveUniversalOutputProgram_fieldCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    rw [show (2 : ℕ) = 1 + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode result)
      (selectiveUniversalOutputProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    exact run_halt_instruction (fuel := 0)
      (selectiveUniversalOutputProgram_controllerAt (pc := 60) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat

/-! ## 4. The two loop steps

The loop head reads the countdown, records which arm it took in register `30`,
runs the reverse pass and lets the one-instruction dispatcher at `25` route the
return.  §4 wraps the head together with the arm it selects, so both steps enter
and leave on the loop's own program counter. -/

private theorem run_selectiveUniversalOutputBodyStep {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (address : BitInput width) (values : List ℕ) (remaining processed : ℕ)
    (maximumBits reverseFuel calleeFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hreverseFuel : reverseFuel = structuralTaggedReverseFuel values.reverse)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveUniversalNodeInput (selectiveStateCode state)
          (descriptionWidth width bound) (processed * rowWidth width bound)
          (boundedCircuitFieldLimit width bound) width (encodeBitInput address)
          (encodeTaggedList values) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hreverseBits : structuralTaggedReverseBits values.reverse ≤ maximumBits)
    (hpairBits :
      natBitLength (Nat.pair 0 (encodeTaggedList values)) ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalNodeInput (selectiveStateCode state)
            (descriptionWidth width bound) (processed * rowWidth width bound)
            (boundedCircuitFieldLimit width bound) width
            (encodeBitInput address) (encodeTaggedList values)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hnextSpineBits :
      natBitLength (encodeTaggedList (result.output :: values.reverse)) ≤
        maximumBits)
    (hcursorBits :
      natBitLength
          (processed * rowWidth width bound + rowWidth width bound) ≤
        maximumBits)
    (hcountBits : natBitLength remaining ≤ maximumBits)
    (hpc : machine.pc = 18)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hrowWidth : machine.registers 10 = rowWidth width bound)
    (hfieldLimit :
      machine.registers 12 = boundedCircuitFieldLimit width bound)
    (hwidth : machine.registers 14 = width)
    (hcount : machine.registers 16 = remaining + 1)
    (haddress : machine.registers 17 = encodeBitInput address)
    (hcursor : machine.registers 18 = processed * rowWidth width bound)
    (hspine : machine.registers 19 = encodeTaggedList values.reverse)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 8 = descriptionWidth width bound →
      resumed.registers 10 = rowWidth width bound →
      resumed.registers 12 = boundedCircuitFieldLimit width bound →
      resumed.registers 14 = width →
      resumed.registers 16 = remaining →
      resumed.registers 17 = encodeBitInput address →
      resumed.registers 18 =
        processed * rowWidth width bound + rowWidth width bound →
      resumed.registers 19 =
        encodeTaggedList (result.output :: values.reverse) →
      runNPOracleProgram selectiveUniversalOutputProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputProgram maximumBits
        (5 +
          (reverseFuel + (1 + (11 + (calleeFuel + (13 + extraFuel))))))
        machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  rw [show 5 + (reverseFuel + (1 + (11 + (calleeFuel + (13 + extraFuel))))) =
    4 + (reverseFuel + (1 + (11 + (calleeFuel + (13 + extraFuel))))) + 1 by
    omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_neg (by rw [hcount]; omega)]
  rw [show 4 + (reverseFuel + (1 + (11 + (calleeFuel + (13 + extraFuel))))) =
    3 + (reverseFuel + (1 + (11 + (calleeFuel + (13 + extraFuel))))) + 1 by
    omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 19) rfl) rfl
    (hsmall 0 (by omega))]
  refine run_selectiveUniversalOutputReverseCall values maximumBits reverseFuel
    _ _ _ hreverseFuel (hsmall 0 (by omega)) hreverseBits hpairBits rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hspine]) ?_
  intro resumed hresumedPc hforward hpreserved
  rw [show 11 + (calleeFuel + (13 + extraFuel)) =
    10 + (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 25) rfl) hresumedPc]
  rw [if_pos (by
    rw [hpreserved 30 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump])]
  refine run_selectiveUniversalOutputNodeCall state result address values
    remaining processed maximumBits calleeFuel extraFuel finalOutput _
    hcalleeRun hsevenBits hrequestBits hwireBits hnextSpineBits hcursorBits
    hcountBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcontinue
  · rw [jump_registers_eq, hpreserved 4 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstateRemaining]
  · rw [jump_registers_eq, hpreserved 6 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hnext]
  · rw [jump_registers_eq, hpreserved 7 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hselected]
  · rw [jump_registers_eq, hpreserved 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, harity]
  · rw [jump_registers_eq, hpreserved 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hrowWidth]
  · rw [jump_registers_eq, hpreserved 12 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
  · rw [jump_registers_eq, hpreserved 14 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hwidth]
  · rw [jump_registers_eq, hpreserved 16 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hcount]
  · rw [jump_registers_eq, hpreserved 17 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, haddress]
  · rw [jump_registers_eq, hpreserved 18 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hcursor]
  · rw [jump_registers_eq, hpreserved 19 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hspine]
  · rw [jump_registers_eq]
    exact hforward

private theorem run_selectiveUniversalOutputExitStep {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (values : List ℕ) (processed : ℕ)
    (maximumBits reverseFuel calleeFuel : ℕ) (machine : NPOracleState)
    (hreverseFuel : reverseFuel = structuralTaggedReverseFuel values.reverse)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode state)
          (descriptionWidth width bound) (processed * rowWidth width bound) 6
          (boundedCircuitFieldLimit width bound) (encodeTaggedList values) →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hreverseBits : structuralTaggedReverseBits values.reverse ≤ maximumBits)
    (hpairBits :
      natBitLength (Nat.pair 0 (encodeTaggedList values)) ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode state)
            (descriptionWidth width bound) (processed * rowWidth width bound) 6
            (boundedCircuitFieldLimit width bound)
            (encodeTaggedList values)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hpc : machine.pc = 18)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hfieldLimit :
      machine.registers 12 = boundedCircuitFieldLimit width bound)
    (hcount : machine.registers 16 = 0)
    (hcursor : machine.registers 18 = processed * rowWidth width bound)
    (hspine : machine.registers 19 = encodeTaggedList values.reverse) :
    runNPOracleProgram selectiveUniversalOutputProgram maximumBits
        (5 + (reverseFuel + (1 + (11 + (calleeFuel + 2))))) machine =
      some (selectiveWireCode result) := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  rw [show 5 + (reverseFuel + (1 + (11 + (calleeFuel + 2)))) =
    4 + (reverseFuel + (1 + (11 + (calleeFuel + 2)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_pos hcount]
  rw [show 4 + (reverseFuel + (1 + (11 + (calleeFuel + 2)))) =
    3 + (reverseFuel + (1 + (11 + (calleeFuel + 2)))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 20) rfl) rfl
    (hsmall 1 (by omega))]
  refine run_selectiveUniversalOutputReverseCall values maximumBits reverseFuel
    _ _ _ hreverseFuel (hsmall 0 (by omega)) hreverseBits hpairBits rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hspine]) ?_
  intro resumed hresumedPc hforward hpreserved
  rw [show 11 + (calleeFuel + 2) = 10 + (calleeFuel + 2) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 25) rfl) hresumedPc]
  rw [if_neg (by
    rw [hpreserved 30 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump])]
  refine run_selectiveUniversalOutputFieldCall state result values processed
    maximumBits calleeFuel _ hcalleeRun hsevenBits hrequestBits hwireBits rfl
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [jump_registers_eq, hpreserved 4 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstateRemaining]
  · rw [jump_registers_eq, hpreserved 6 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hnext]
  · rw [jump_registers_eq, hpreserved 7 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hselected]
  · rw [jump_registers_eq, hpreserved 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, harity]
  · rw [jump_registers_eq, hpreserved 12 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
  · rw [jump_registers_eq, hpreserved 18 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hcursor]
  · rw [jump_registers_eq]
    exact hforward

/-! ## 5. The loop

Interpreter resources on this level are data dependent, so the loop's clock and
its register-width envelope are defined by the same recursion as its output. -/

/-- Interpreter fuel of the controller from the loop head. -/
private def universalOutputLoopFuel {width bound : ℕ}
    (nodeRunner : SelectiveUniversalNodeRunner width bound)
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (address : BitInput width) (outputRow : Fin (bound + 1)) :
    (remaining processed : ℕ) → processed + remaining ≤ bound →
      SelectiveState (descriptionWidth width bound) → List ℕ → ℕ
  | 0, _, _, state, values =>
      5 +
        (structuralTaggedReverseFuel values.reverse +
          (1 +
            (11 +
              (fieldRunner.fuel state outputRow 6
                (boundedCircuitFieldLimit width bound)
                (universalOutputFieldBlock width bound) values + 2))))
  | remaining + 1, processed, hbound, state, values =>
      5 +
        (structuralTaggedReverseFuel values.reverse +
          (1 +
            (11 +
              (nodeRunner.fuel state ⟨processed, by omega⟩ address values +
                (13 +
                  universalOutputLoopFuel nodeRunner fieldRunner address
                    outputRow remaining (processed + 1) (by omega)
                    (selectiveCompileUniversalNode state ⟨processed, by omega⟩
                      address values).state
                    (values ++
                      [(selectiveCompileUniversalNode state
                        ⟨processed, by omega⟩ address values).output]))))))

/-- Register width of the controller from the loop head. -/
private def universalOutputLoopBits {width bound : ℕ}
    (nodeRunner : SelectiveUniversalNodeRunner width bound)
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (address : BitInput width) (outputRow : Fin (bound + 1)) :
    (remaining processed : ℕ) → processed + remaining ≤ bound →
      SelectiveState (descriptionWidth width bound) → List ℕ → ℕ
  | 0, processed, _, state, values =>
      max (structuralTaggedReverseBits values.reverse) <|
        max (natBitLength (Nat.pair 0 (encodeTaggedList values))) <|
          max
            (natBitLength
              (selectiveFieldSelectInput (selectiveStateCode state)
                (descriptionWidth width bound)
                (processed * rowWidth width bound) 6
                (boundedCircuitFieldLimit width bound)
                (encodeTaggedList values))) <|
            max
              (natBitLength
                (Nat.pair 0
                  (selectiveWireCode
                    (selectiveCompileFirstFieldSelect state outputRow
                      values)))) <|
              fieldRunner.bits state outputRow 6
                (boundedCircuitFieldLimit width bound)
                (universalOutputFieldBlock width bound) values
  | remaining + 1, processed, hbound, state, values =>
      max (structuralTaggedReverseBits values.reverse) <|
        max (natBitLength (Nat.pair 0 (encodeTaggedList values))) <|
          max
            (natBitLength
              (selectiveUniversalNodeInput (selectiveStateCode state)
                (descriptionWidth width bound)
                (processed * rowWidth width bound)
                (boundedCircuitFieldLimit width bound) width
                (encodeBitInput address) (encodeTaggedList values))) <|
            max
              (natBitLength
                (Nat.pair 0
                  (selectiveWireCode
                    (selectiveCompileUniversalNode state ⟨processed, by omega⟩
                      address values)))) <|
              max
                (nodeRunner.bits state ⟨processed, by omega⟩ address values) <|
                max
                  (natBitLength
                    (encodeTaggedList
                      ((selectiveCompileUniversalNode state
                        ⟨processed, by omega⟩ address values).output ::
                        values.reverse))) <|
                  max
                    (natBitLength
                      (processed * rowWidth width bound +
                        rowWidth width bound)) <|
                    max (natBitLength remaining) <|
                      universalOutputLoopBits nodeRunner fieldRunner address
                        outputRow remaining (processed + 1) (by omega)
                        (selectiveCompileUniversalNode state
                          ⟨processed, by omega⟩ address values).state
                        (values ++
                          [(selectiveCompileUniversalNode state
                            ⟨processed, by omega⟩ address values).output])

set_option maxHeartbeats 1600000 in
-- The loop is one induction on the remaining rows; each step is discharged by
-- one of §4's two traces.
private theorem run_selectiveUniversalOutputLoop {width bound : ℕ}
    (nodeRunner : SelectiveUniversalNodeRunner width bound)
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (address : BitInput width) (outputRow : Fin (bound + 1))
    (maximumBits : ℕ) (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (remaining processed : ℕ) (hbound : processed + remaining ≤ bound)
      (state : SelectiveState (descriptionWidth width bound))
      (values : List ℕ) (machine : NPOracleState),
      selectiveStateOrdered state →
      outputRow.val = processed + remaining →
      universalOutputLoopBits nodeRunner fieldRunner address outputRow remaining
          processed hbound state values ≤ maximumBits →
      machine.pc = 18 →
      machine.registers 4 = state.target - state.next →
      machine.registers 6 = state.next →
      machine.registers 7 = selectiveSelectedCode state.selected →
      machine.registers 8 = descriptionWidth width bound →
      machine.registers 10 = rowWidth width bound →
      machine.registers 12 = boundedCircuitFieldLimit width bound →
      machine.registers 14 = width →
      machine.registers 16 = remaining →
      machine.registers 17 = encodeBitInput address →
      machine.registers 18 = processed * rowWidth width bound →
      machine.registers 19 = encodeTaggedList values.reverse →
      runNPOracleProgram selectiveUniversalOutputProgram maximumBits
          (universalOutputLoopFuel nodeRunner fieldRunner address outputRow
            remaining processed hbound state values) machine =
        some
          (selectiveWireCode
            (universalOutputWire address outputRow remaining processed hbound
              state values)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro processed hbound state values machine hordered houtputRow hbits hpc
        hstateRemaining hnext hselected harity hrowWidth hfieldLimit hwidth
        hcount haddress hcursor hspine
      simp only [universalOutputLoopBits] at hbits
      have hreverseBits := (Nat.le_max_left _ _).trans hbits
      have htail0 := (Nat.le_max_right _ _).trans hbits
      have hpairBits := (Nat.le_max_left _ _).trans htail0
      have htail1 := (Nat.le_max_right _ _).trans htail0
      have hrequestBits := (Nat.le_max_left _ _).trans htail1
      have htail2 := (Nat.le_max_right _ _).trans htail1
      have hwireBits := (Nat.le_max_left _ _).trans htail2
      have hcalleeBits := (Nat.le_max_right _ _).trans htail2
      simp only [universalOutputLoopFuel, universalOutputWire,
        universalOutputNodes]
      refine run_selectiveUniversalOutputExitStep state
        (selectiveCompileFirstFieldSelect state outputRow values) values
        processed maximumBits _ _ _ rfl ?_ hsevenBits hreverseBits hpairBits
        hrequestBits hwireBits hpc hstateRemaining hnext hselected harity
        hfieldLimit hcount hcursor hspine
      have hrow : outputRow.val = processed := by omega
      intro frame hframePc hframeInput
      refine run_bits_mono
        (fieldRunner.executes state outputRow 6
          (boundedCircuitFieldLimit width bound) values
          (universalOutputFieldBlock width bound) hordered frame hframePc ?_)
        hcalleeBits
      rw [hrow]
      exact hframeInput
  | succ remaining inductionHypothesis =>
      intro processed hbound state values machine hordered houtputRow hbits hpc
        hstateRemaining hnext hselected harity hrowWidth hfieldLimit hwidth
        hcount haddress hcursor hspine
      simp only [universalOutputLoopBits] at hbits
      have hreverseBits := (Nat.le_max_left _ _).trans hbits
      have htail0 := (Nat.le_max_right _ _).trans hbits
      have hpairBits := (Nat.le_max_left _ _).trans htail0
      have htail1 := (Nat.le_max_right _ _).trans htail0
      have hrequestBits := (Nat.le_max_left _ _).trans htail1
      have htail2 := (Nat.le_max_right _ _).trans htail1
      have hwireBits := (Nat.le_max_left _ _).trans htail2
      have htail3 := (Nat.le_max_right _ _).trans htail2
      have hcalleeBits := (Nat.le_max_left _ _).trans htail3
      have htail4 := (Nat.le_max_right _ _).trans htail3
      have hnextSpineBits := (Nat.le_max_left _ _).trans htail4
      have htail5 := (Nat.le_max_right _ _).trans htail4
      have hcursorBits := (Nat.le_max_left _ _).trans htail5
      have htail6 := (Nat.le_max_right _ _).trans htail5
      have hcountBits := (Nat.le_max_left _ _).trans htail6
      have hrecursiveBits := (Nat.le_max_right _ _).trans htail6
      rw [universalOutputWire_succ]
      simp only [universalOutputLoopFuel]
      refine run_selectiveUniversalOutputBodyStep state
        (selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
          values) address values remaining processed maximumBits _ _ _ _ _ rfl
        ?_ hsevenBits hreverseBits hpairBits hrequestBits hwireBits
        hnextSpineBits hcursorBits hcountBits hpc hstateRemaining hnext
        hselected harity hrowWidth hfieldLimit hwidth hcount haddress hcursor
        hspine ?_
      · intro frame hframePc hframeInput
        exact run_bits_mono
          (nodeRunner.executes state ⟨processed, by omega⟩ address values
            hordered frame hframePc hframeInput) hcalleeBits
      · intro final hfinalPc hfinalRemaining hfinalNext hfinalSelected
          hfinalArity hfinalRowWidth hfinalFieldLimit hfinalWidth hfinalCount
          hfinalAddress hfinalCursor hfinalSpine
        refine inductionHypothesis (processed + 1) (by omega)
          (selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
            values).state
          (values ++
            [(selectiveCompileUniversalNode state ⟨processed, by omega⟩ address
              values).output]) final
          (selectiveCompileUniversalNode_ordered state ⟨processed, by omega⟩
            address values hordered)
          (by rw [houtputRow]; omega) hrecursiveBits hfinalPc hfinalRemaining
          hfinalNext hfinalSelected hfinalArity hfinalRowWidth hfinalFieldLimit
          hfinalWidth hfinalCount hfinalAddress ?_ ?_
        · rw [hfinalCursor]
          ring
        · rw [hfinalSpine]
          simp

set_option maxHeartbeats 1600000 in
-- Sixteen unpair steps and two zeroing steps set up the loop's registers.
private theorem run_selectiveUniversalOutputPrologue {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (address : BitInput width) (count : ℕ)
    (maximumBits loopFuel finalOutput : ℕ) (entry : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalOutputInput (selectiveStateCode state)
            (descriptionWidth width bound) (rowWidth width bound)
            (boundedCircuitFieldLimit width bound) width count
            (encodeBitInput address)) ≤
        maximumBits)
    (hpc : entry.pc = 0)
    (hinput :
      entry.registers 0 =
        selectiveUniversalOutputInput (selectiveStateCode state)
          (descriptionWidth width bound) (rowWidth width bound)
          (boundedCircuitFieldLimit width bound) width count
          (encodeBitInput address))
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 = state.target - state.next →
      resumed.registers 6 = state.next →
      resumed.registers 7 = selectiveSelectedCode state.selected →
      resumed.registers 8 = descriptionWidth width bound →
      resumed.registers 10 = rowWidth width bound →
      resumed.registers 12 = boundedCircuitFieldLimit width bound →
      resumed.registers 14 = width →
      resumed.registers 16 = count →
      resumed.registers 17 = encodeBitInput address →
      resumed.registers 18 = 0 →
      resumed.registers 19 = 0 →
      runNPOracleProgram selectiveUniversalOutputProgram maximumBits loopFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalOutputProgram maximumBits
        (18 + loopFuel) entry =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveUniversalOutputInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have hrowWidthBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hfieldLimitBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hwidthBits := natBitLength_pair_left hfour
  have hfive := natBitLength_pair_right hfour
  have hcountBits := natBitLength_pair_left hfive
  have haddressBits := natBitLength_pair_right hfive
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show 18 + loopFuel = 17 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveUniversalOutputProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveUniversalOutputInput]) hstateBits]
  rw [show 17 + loopFuel = 16 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (descriptionWidth width bound) <|
        Nat.pair (rowWidth width bound) <|
          Nat.pair (boundedCircuitFieldLimit width bound) <|
            Nat.pair width (Nat.pair count (encodeBitInput address)))
    (selectiveUniversalOutputProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveUniversalOutputInput])
    hone]
  rw [show 16 + loopFuel = 15 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveUniversalOutputProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 15 + loopFuel = 14 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalOutputProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [show 14 + loopFuel = 13 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveUniversalOutputProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 13 + loopFuel = 12 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveUniversalOutputProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [show 12 + loopFuel = 11 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := descriptionWidth width bound)
    (selectiveUniversalOutputProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 11 + loopFuel = 10 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (rowWidth width bound) <|
        Nat.pair (boundedCircuitFieldLimit width bound) <|
          Nat.pair width (Nat.pair count (encodeBitInput address)))
    (selectiveUniversalOutputProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [show 10 + loopFuel = 9 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowWidth width bound)
    (selectiveUniversalOutputProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [show 9 + loopFuel = 8 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound) <|
        Nat.pair width (Nat.pair count (encodeBitInput address)))
    (selectiveUniversalOutputProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 8 + loopFuel = 7 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := boundedCircuitFieldLimit width bound)
    (selectiveUniversalOutputProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [show 7 + loopFuel = 6 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair count (encodeBitInput address)))
    (selectiveUniversalOutputProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [show 6 + loopFuel = 5 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (selectiveUniversalOutputProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show 5 + loopFuel = 4 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair count (encodeBitInput address))
    (selectiveUniversalOutputProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [show 4 + loopFuel = 3 + loopFuel + 1 by omega]
  rw [run_unpairLeft_instruction (value := count)
    (selectiveUniversalOutputProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [show 3 + loopFuel = 2 + loopFuel + 1 by omega]
  rw [run_unpairRight_instruction (value := encodeBitInput address)
    (selectiveUniversalOutputProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) haddressBits]
  rw [show 2 + loopFuel = 1 + loopFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 16) rfl) rfl
    (hsmall 0 (by omega))]
  rw [show 1 + loopFuel = loopFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalOutputProgram_controllerAt (pc := 17) rfl) rfl
    (hsmall 0 (by omega))]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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

/-- **Level premise.**  The universal evaluator's output compiler compiles every
row of one described DAG and selects the evaluator's output wire, at its own ABI
frame, at an arbitrary entry state. -/
structure SelectiveUniversalOutputRunner (width bound : ℕ) where
  /-- Register width of one whole-evaluator compilation. -/
  bits : SelectiveState (descriptionWidth width bound) → BitInput width →
    ∀ count : ℕ, count ≤ bound → ℕ
  /-- Interpreter fuel of one whole-evaluator compilation. -/
  fuel : SelectiveState (descriptionWidth width bound) → BitInput width →
    ∀ count : ℕ, count ≤ bound → ℕ
  /-- The published run, at an arbitrary entry state. -/
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (address : BitInput width) (count : ℕ) (hcount : count ≤ bound),
      selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveUniversalOutputInput (selectiveStateCode state)
        (descriptionWidth width bound) (rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width count
        (encodeBitInput address) →
    runNPOracleProgram selectiveUniversalOutputProgram
        (bits state address count hcount) (fuel state address count hcount)
        entry =
      some
        (selectiveWireCode
          (selectiveCompileUniversalOutput state address count hcount))

/-- Register width of one whole-evaluator compilation. -/
def selectiveUniversalOutputRunBits {width bound : ℕ}
    (nodeRunner : SelectiveUniversalNodeRunner width bound)
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (state : SelectiveState (descriptionWidth width bound))
    (address : BitInput width) (count : ℕ) (hcount : count ≤ bound) : ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveUniversalOutputInput (selectiveStateCode state)
          (descriptionWidth width bound) (rowWidth width bound)
          (boundedCircuitFieldLimit width bound) width count
          (encodeBitInput address))) <|
      universalOutputLoopBits nodeRunner fieldRunner address
        ⟨count, by omega⟩ count 0 (by omega) state []

/-- Interpreter fuel of one whole-evaluator compilation. -/
def selectiveUniversalOutputRunFuel {width bound : ℕ}
    (nodeRunner : SelectiveUniversalNodeRunner width bound)
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (state : SelectiveState (descriptionWidth width bound))
    (address : BitInput width) (count : ℕ) (hcount : count ≤ bound) : ℕ :=
  18 +
    universalOutputLoopFuel nodeRunner fieldRunner address ⟨count, by omega⟩
      count 0 (by omega) state []

/-- **The universal evaluator's output compiler run, from the two levels below
it.**  The `909`-instruction stream compiles exactly the evaluator the source
compiler produces.  Only the row compiler and the field selector remain as
premises; the tagged reverse pass is consumed opaquely. -/
def selectiveUniversalOutputRunnerOfLevels {width bound : ℕ}
    (nodeRunner : SelectiveUniversalNodeRunner width bound)
    (fieldRunner : SelectiveFieldSelectRunner width bound) :
    SelectiveUniversalOutputRunner width bound where
  bits := selectiveUniversalOutputRunBits nodeRunner fieldRunner
  fuel := selectiveUniversalOutputRunFuel nodeRunner fieldRunner
  executes := by
    intro state address count hcount hordered entry hentryPc hentryInput
    have hsevenBits :
        natBitLength 7 ≤
          selectiveUniversalOutputRunBits nodeRunner fieldRunner state address
            count hcount :=
      Nat.le_max_left _ _
    have htail0 :
        max
            (natBitLength
              (selectiveUniversalOutputInput (selectiveStateCode state)
                (descriptionWidth width bound) (rowWidth width bound)
                (boundedCircuitFieldLimit width bound) width count
                (encodeBitInput address)))
            (universalOutputLoopBits nodeRunner fieldRunner address
              ⟨count, by omega⟩ count 0 (by omega) state []) ≤
          selectiveUniversalOutputRunBits nodeRunner fieldRunner state address
            count hcount :=
      Nat.le_max_right _ _
    have hrequestBits := (Nat.le_max_left _ _).trans htail0
    have hloopBits := (Nat.le_max_right _ _).trans htail0
    have hzero : 0 + count ≤ bound := by omega
    have hlt : count < bound + 1 := by omega
    have hnodes :
        universalOutputNodes address count 0 hzero state [] =
          selectiveCompileUniversalNodes state address count hcount :=
      universalOutputNodes_eq address state count 0 count hzero (by omega)
        hcount (by omega)
    have houtput :
        universalOutputWire address ⟨count, hlt⟩ count 0 hzero state [] =
          selectiveCompileUniversalOutput state address count hcount := by
      unfold universalOutputWire
      rw [hnodes]
      rfl
    rw [← houtput]
    unfold selectiveUniversalOutputRunFuel
    refine run_selectiveUniversalOutputPrologue state address count _ _ _ entry
      hsevenBits hrequestBits hentryPc hentryInput ?_
    intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
      hresumedArity hresumedRowWidth hresumedFieldLimit hresumedWidth
      hresumedCount hresumedAddress hresumedCursor hresumedSpine
    refine run_selectiveUniversalOutputLoop nodeRunner fieldRunner address
      ⟨count, hlt⟩ _ hsevenBits count 0 hzero state [] resumed
      hordered (by simp) hloopBits hresumedPc hresumedRemaining hresumedNext
      hresumedSelected hresumedArity hresumedRowWidth hresumedFieldLimit
      hresumedWidth hresumedCount hresumedAddress ?_ ?_
    · rw [hresumedCursor]
      simp
    · rw [hresumedSpine]
      simp [encodeTaggedList]

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
