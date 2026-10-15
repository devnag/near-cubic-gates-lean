import Proof.Supplier.SelectiveUnaryRun
import Proof.Supplier.SelectiveFieldSelectRun
import Proof.Supplier.SelectiveAddressSelectRun
import Batteries.Tactic.OpenPrivate

/-!
# The universal-evaluator row compiler's run

`selectiveUniversalNodeProgram` is the `641`-instruction stream that compiles
one described DAG row.  It is a controller of `135` instructions with four
relocated callees: the `196`-instruction field selector, the `97`-instruction
unary-equality compiler, the `195`-instruction address selector, and the
`18`-instruction append transition.

The controller is straight line.  It runs the two field selectors that pick the
row's left and right children, the unary test that decides a constant row, the
address selector that evaluates an input row, three appends for the negation,
conjunction and disjunction cases, and one final field selection that dispatches
on the row's tag.  All eight calls return to one physical block at `112` and are
routed back by a phase dispatcher at `119`.

This module executes that controller.  The unary compiler's already closed run
and the append transition are consumed opaquely; the field selector and the
address selector are named runner premises one level down.
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

open private selectiveUniversalNodeInput selectiveUniversalNodeControllerProgram
  selectiveUniversalNodeControllerProgram_length selectiveUniversalNodeProgram
  selectiveFieldSelectInput selectiveFieldSelectProgram
  selectiveFieldSelectProgram_length selectiveAddressSelectInput
  selectiveAddressSelectProgram selectiveAddressSelectProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

open private selectiveCompileGuardedAny_ordered from
  Proof.Supplier.SelectiveCountCasesRun

/-! ## 1. The two level premises one level further down

`SelectiveFieldSelectRunner` and `SelectiveAddressSelectRunner` are imported
from their owning level modules (`SelectiveFieldSelectRun`,
`SelectiveAddressSelectRun`), which also discharge them outright. -/

/-! ## 2. Decoding the fixed 641-instruction stream

The controller occupies the first `135` positions, the field selector the next
`196`, the unary compiler the next `97`, the address selector the next `195`,
and the append transition the last `18`.  Every later step decodes through
exactly one of the five lemmas below. -/

private theorem selectiveEmitProgram_length_eq :
    selectiveEmitProgram.length = 18 := by
  rfl

private theorem selectiveUniversalNodeProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveUniversalNodeControllerProgram 135 331 428 623)[pc]? =
        some instruction) :
    selectiveUniversalNodeProgram[pc]? = some instruction := by
  have hpc :
      pc < (selectiveUniversalNodeControllerProgram 135 331 428 623).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUniversalNodeControllerProgram_length] at hpc
  simp only [selectiveUniversalNodeProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length,
      selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveUniversalNodeControllerProgram_length]
    omega)]
  exact hlookup

theorem selectiveUniversalNodeProgram_fieldCallable :
    ProgramCallableAt selectiveUniversalNodeProgram selectiveFieldSelectProgram
      135 1000 50 112 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveFieldSelectProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveFieldSelectProgram_length] at hpc
  simp only [selectiveUniversalNodeProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length,
      selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveUniversalNodeControllerProgram_length]
    omega)]
  simp only [selectiveUniversalNodeControllerProgram_length]
  rw [show 135 + pc - 135 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveUniversalNodeProgram_unaryCallable :
    ProgramCallableAt selectiveUniversalNodeProgram selectiveUnaryProgram
      331 5000 50 112 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUnaryProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUnaryProgram_length] at hpc
  simp only [selectiveUniversalNodeProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length,
      selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalNodeControllerProgram_length,
    selectiveFieldSelectProgram_length]
  rw [show 331 + pc - (135 + 196) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveUniversalNodeProgram_addressCallable :
    ProgramCallableAt selectiveUniversalNodeProgram
      selectiveAddressSelectProgram 428 7000 50 112 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveAddressSelectProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveAddressSelectProgram_length] at hpc
  simp only [selectiveUniversalNodeProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length,
      selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalNodeControllerProgram_length,
    selectiveFieldSelectProgram_length, selectiveUnaryProgram_length]
  rw [show 428 + pc - (135 + 196 + 97) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveUniversalNodeProgram_emitCallable :
    ProgramCallableAt selectiveUniversalNodeProgram selectiveEmitProgram
      623 10000 50 112 := by
  intro pc instruction hlookup
  simp only [selectiveUniversalNodeProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveUniversalNodeControllerProgram_length,
      selectiveFieldSelectProgram_length, selectiveUnaryProgram_length,
      selectiveAddressSelectProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveUniversalNodeControllerProgram_length,
    selectiveFieldSelectProgram_length, selectiveUnaryProgram_length,
    selectiveAddressSelectProgram_length]
  rw [show 623 + pc - (135 + 196 + 97 + 195) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The row's eight compiled stages, at the typed level

`selectiveCompileUniversalNode` is a fixed composition of seven compiler stages
followed by one guarded selection over their live outputs.  §3 names each stage
and states the tag dispatch as a field selection, which is the shape the
controller's last call produces. -/

/-- The first field selector's wire: the row's left child. -/
def universalNodeLeft {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileFirstFieldSelect state row priorValues

/-- The second field selector's wire: the row's right child. -/
def universalNodeRight {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileSecondFieldSelect
    (universalNodeLeft state row priorValues).state row priorValues

/-- The unary test that decides a constant row. -/
def universalNodeConstant {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileExpr (universalNodeRight state row priorValues).state
    (firstFieldEqualsExpr row 1)

/-- The address selector's wire: the value of an input row. -/
def universalNodeInputValue {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCompileExpr (universalNodeConstant state row priorValues).state
    (constantAddressSelectionExpr row address)

/-- The negation case. -/
def universalNodeNegated {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveNot (universalNodeInputValue state row address priorValues).state
    (universalNodeLeft state row priorValues).output

/-- The conjunction case. -/
def universalNodeConjunction {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveAnd (universalNodeNegated state row address priorValues).state
    (universalNodeLeft state row priorValues).output
    (universalNodeRight state row priorValues).output

/-- The disjunction case. -/
def universalNodeDisjunction {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveOr (universalNodeConjunction state row address priorValues).state
    (universalNodeLeft state row priorValues).output
    (universalNodeRight state row priorValues).output

/-- The five live case wires the tag dispatch selects between. -/
def universalNodeCases {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width)
    (priorValues : List ℕ) : List ℕ :=
  [ (universalNodeConstant state row priorValues).output
  , (universalNodeInputValue state row address priorValues).output
  , (universalNodeNegated state row address priorValues).output
  , (universalNodeConjunction state row address priorValues).output
  , (universalNodeDisjunction state row address priorValues).output
  ]

private theorem universalNodeFirstBlock (width bound : ℕ) :
    6 + boundedCircuitFieldLimit width bound ≤ rowWidth width bound := by
  change 6 + boundedCircuitFieldLimit width bound ≤
    6 + 2 * boundedCircuitFieldLimit width bound
  omega

private theorem universalNodeSecondBlock (width bound : ℕ) :
    6 + boundedCircuitFieldLimit width bound +
        boundedCircuitFieldLimit width bound ≤
      rowWidth width bound := by
  change 6 + boundedCircuitFieldLimit width bound +
      boundedCircuitFieldLimit width bound ≤
    6 + 2 * boundedCircuitFieldLimit width bound
  omega

private theorem universalNodeTagBlock (width bound : ℕ) :
    0 + 6 ≤ rowWidth width bound := by
  change 0 + 6 ≤ 6 + 2 * boundedCircuitFieldLimit width bound
  omega

/-- **The controller's scheduling identity.**  The source compiler's tag
dispatch is exactly a field selection over the five live case wires. -/
theorem selectiveCompileUniversalNode_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width)
    (priorValues : List ℕ) :
    selectiveCompileUniversalNode state row address priorValues =
      selectiveCompileFieldSelect
        (universalNodeDisjunction state row address priorValues).state
        (fun candidate value =>
          unaryEqualsExpr candidate 0 6 value (universalNodeTagBlock width bound))
        row (universalNodeCases state row address priorValues) := by
  rfl

theorem universalNodeLeft_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered (universalNodeLeft state row priorValues).state :=
  selectiveCompileGuardedAny_ordered _ state hordered

theorem universalNodeRight_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered (universalNodeRight state row priorValues).state :=
  selectiveCompileGuardedAny_ordered _ _
    (universalNodeLeft_ordered state row priorValues hordered)

theorem universalNodeConstant_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered (universalNodeConstant state row priorValues).state :=
  selectiveCompileExpr_ordered _ _
    (universalNodeRight_ordered state row priorValues hordered)

theorem universalNodeInputValue_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (universalNodeInputValue state row address priorValues).state :=
  selectiveCompileExpr_ordered _ _
    (universalNodeConstant_ordered state row priorValues hordered)

theorem universalNodeNegated_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (universalNodeNegated state row address priorValues).state :=
  selectiveState_emit_ordered _ _
    (universalNodeInputValue_ordered state row address priorValues hordered)

theorem universalNodeConjunction_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (universalNodeConjunction state row address priorValues).state :=
  selectiveState_emit_ordered _ _
    (universalNodeNegated_ordered state row address priorValues hordered)

theorem universalNodeDisjunction_ordered {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (universalNodeDisjunction state row address priorValues).state :=
  selectiveState_emit_ordered _ _
    (universalNodeConjunction_ordered state row address priorValues hordered)

/-! ## 4. The shared return block and the four call frames

All four callees return to the same physical block at `112`, which unpacks the
returned wire into the controller's live state registers and falls through to
the phase dispatcher at `119`.  §4 proves that block once, then wraps it in one
call-frame lemma per physical request-building block.  Each frame consumes its
callee's run as a hypothesis, so nothing here depends on which level supplies
it. -/

-- Seven steps unpacking the returned wire back into the live state registers.
private theorem run_selectiveUniversalNodeReturn {width bound : ℕ}
    (result : SelectiveWire (descriptionWidth width bound))
    (maximumBits extraFuel finalOutput : ℕ) (mid : NPOracleState)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hpc : mid.pc = 112)
    (haccumulator :
      mid.registers 50 = Nat.pair 0 (selectiveWireCode result))
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 119 →
      resumed.registers 0 = selectiveWireCode result →
      resumed.registers 2 = selectiveStateCode result.state →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 25 = result.output →
      (∀ index : ℕ, index ≠ 0 → index ≠ 2 → index ≠ 4 → index ≠ 5 →
        index ≠ 6 → index ≠ 7 → index ≠ 25 →
        resumed.registers index = mid.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (7 + extraFuel) mid =
      some finalOutput := by
  have hstateForm :
      selectiveStateCode result.state =
        Nat.pair (result.state.target - result.state.next)
          (Nat.pair result.state.next
            (selectiveSelectedCode result.state.selected)) := rfl
  have hwireForm :
      selectiveWireCode result =
        Nat.pair (selectiveStateCode result.state) result.output := rfl
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  rw [hwireForm] at hwireParts
  have hstateBits := natBitLength_pair_left hwireParts
  have houtputBits := natBitLength_pair_right hwireParts
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailBits
  have hselectedBits := natBitLength_pair_right htailBits
  rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveWireCode result)
    (selectiveUniversalNodeProgram_controllerAt (pc := 112) rfl) hpc
    (by rw [haccumulator]; simp) hwireFlat]
  rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode result.state)
    (selectiveUniversalNodeProgram_controllerAt (pc := 113) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwireForm]) hstateBits]
  rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
  rw [run_unpairRight_instruction (value := result.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 114) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwireForm]) houtputBits]
  rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
  rw [run_unpairLeft_instruction
    (value := result.state.target - result.state.next)
    (selectiveUniversalNodeProgram_controllerAt (pc := 115) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair result.state.next
        (selectiveSelectedCode result.state.selected))
    (selectiveUniversalNodeProgram_controllerAt (pc := 116) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailBits]
  rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
  rw [run_unpairLeft_instruction (value := result.state.next)
    (selectiveUniversalNodeProgram_controllerAt (pc := 117) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode result.state.selected)
    (selectiveUniversalNodeProgram_controllerAt (pc := 118) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro index h0 h2 h4 h5 h6 h7 h25
    simp [NPOracleState.write, NPOracleState.jump, h0, h2, h4, h5, h6, h7, h25]

-- Nine request-building steps around the relocated field selector.
private theorem run_selectiveUniversalNodeFieldCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (rowBase start limit valuesCode : ℕ)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode state)
          (descriptionWidth width bound) rowBase start limit valuesCode →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hrequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode state)
            (descriptionWidth width bound) rowBase start limit valuesCode) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hpc : machine.pc = 79)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hrowBase : machine.registers 10 = rowBase)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hvalues : machine.registers 18 = valuesCode)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 119 →
      resumed.registers 0 = selectiveWireCode result →
      resumed.registers 2 = selectiveStateCode result.state →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 25 = result.output →
      (∀ index : ℕ, index < 1000 ∧ index ≠ 0 ∧ index ≠ 2 ∧ index ≠ 4 ∧
        index ≠ 5 ∧ index ≠ 6 ∧ index ≠ 7 ∧ index ≠ 22 ∧ index ≠ 23 ∧
        index ≠ 25 ∧ index ≠ 31 ∧ index ≠ 50 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (9 + (calleeFuel + (7 + extraFuel))) machine =
      some finalOutput := by
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
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  rw [show 9 + (calleeFuel + (7 + extraFuel)) =
    8 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalNodeProgram_controllerAt (pc := 79) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 8 + (calleeFuel + (7 + extraFuel)) =
    7 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalNodeProgram_controllerAt (pc := 80) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hremaining, hstateForm])
    hstateBits]
  rw [show 7 + (calleeFuel + (7 + extraFuel)) =
    6 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair limit valuesCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 81) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit, hvalues]) hfour]
  rw [show 6 + (calleeFuel + (7 + extraFuel)) =
    5 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair start (Nat.pair limit valuesCode))
    (selectiveUniversalNodeProgram_controllerAt (pc := 82) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) hthree]
  rw [show 5 + (calleeFuel + (7 + extraFuel)) =
    4 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair rowBase (Nat.pair start (Nat.pair limit valuesCode)))
    (selectiveUniversalNodeProgram_controllerAt (pc := 83) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htwo]
  rw [show 4 + (calleeFuel + (7 + extraFuel)) =
    3 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair rowBase (Nat.pair start (Nat.pair limit valuesCode))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 84) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [show 3 + (calleeFuel + (7 + extraFuel)) =
    2 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveFieldSelectInput (selectiveStateCode state)
        (descriptionWidth width bound) rowBase start limit valuesCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 85) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, selectiveFieldSelectInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (7 + extraFuel)) =
    1 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 86) rfl) rfl hzeroBits]
  rw [show 1 + (calleeFuel + (7 + extraFuel)) =
    calleeFuel + (7 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 87) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveFieldSelectProgram)
    (calleeOutput := selectiveWireCode result)
    selectiveUniversalNodeProgram_fieldCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    refine run_selectiveUniversalNodeReturn result maximumBits extraFuel
      finalOutput _ hwireBits (by simp [NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) ?_
    intro resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut hpreserved
    refine hcontinue resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut ?_
    intro index hind
    obtain ⟨hlt, h0, h2, h4, h5, h6, h7, h22, h23, h25, h31, h50⟩ := hind
    have hlow : ¬ (1000 ≤ index) := by omega
    have hframe : index ≠ 1000 := by omega
    rw [hpreserved index h0 h2 h4 h5 h6 h7 h25]
    simp [NPOracleState.write, NPOracleState.jump, relocateState, hlow, hframe,
      h22, h23, h31, h50]

-- Nine request-building steps around the relocated unary-equality compiler.
private theorem run_selectiveUniversalNodeUnaryCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (rowBase start limit value : ℕ)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveUnaryInput (selectiveStateCode state)
          (descriptionWidth width bound) rowBase start limit value →
      runNPOracleProgram selectiveUnaryProgram maximumBits calleeFuel frame =
        some (selectiveWireCode result))
    (hrequestBits :
      natBitLength
          (selectiveUnaryInput (selectiveStateCode state)
            (descriptionWidth width bound) rowBase start limit value) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hpc : machine.pc = 88)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hrowBase : machine.registers 10 = rowBase)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hvalue : machine.registers 17 = value)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 119 →
      resumed.registers 0 = selectiveWireCode result →
      resumed.registers 2 = selectiveStateCode result.state →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 25 = result.output →
      (∀ index : ℕ, index < 1000 ∧ index ≠ 0 ∧ index ≠ 2 ∧ index ≠ 4 ∧
        index ≠ 5 ∧ index ≠ 6 ∧ index ≠ 7 ∧ index ≠ 22 ∧ index ≠ 23 ∧
        index ≠ 25 ∧ index ≠ 31 ∧ index ≠ 50 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (9 + (calleeFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveUnaryInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  rw [show 9 + (calleeFuel + (7 + extraFuel)) =
    8 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalNodeProgram_controllerAt (pc := 88) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 8 + (calleeFuel + (7 + extraFuel)) =
    7 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalNodeProgram_controllerAt (pc := 89) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hremaining, hstateForm])
    hstateBits]
  rw [show 7 + (calleeFuel + (7 + extraFuel)) =
    6 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair limit value)
    (selectiveUniversalNodeProgram_controllerAt (pc := 90) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit, hvalue]) hfour]
  rw [show 6 + (calleeFuel + (7 + extraFuel)) =
    5 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair start (Nat.pair limit value))
    (selectiveUniversalNodeProgram_controllerAt (pc := 91) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) hthree]
  rw [show 5 + (calleeFuel + (7 + extraFuel)) =
    4 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair rowBase (Nat.pair start (Nat.pair limit value)))
    (selectiveUniversalNodeProgram_controllerAt (pc := 92) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htwo]
  rw [show 4 + (calleeFuel + (7 + extraFuel)) =
    3 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair rowBase (Nat.pair start (Nat.pair limit value))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 93) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [show 3 + (calleeFuel + (7 + extraFuel)) =
    2 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveUnaryInput (selectiveStateCode state)
        (descriptionWidth width bound) rowBase start limit value)
    (selectiveUniversalNodeProgram_controllerAt (pc := 94) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectiveUnaryInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (7 + extraFuel)) =
    1 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 95) rfl) rfl hzeroBits]
  rw [show 1 + (calleeFuel + (7 + extraFuel)) =
    calleeFuel + (7 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 96) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveUnaryProgram)
    (calleeOutput := selectiveWireCode result)
    selectiveUniversalNodeProgram_unaryCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    refine run_selectiveUniversalNodeReturn result maximumBits extraFuel
      finalOutput _ hwireBits (by simp [NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) ?_
    intro resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut hpreserved
    refine hcontinue resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut ?_
    intro index hind
    obtain ⟨hlt, h0, h2, h4, h5, h6, h7, h22, h23, h25, h31, h50⟩ := hind
    have hlow : ¬ (5000 ≤ index) := by omega
    have hframe : index ≠ 5000 := by omega
    rw [hpreserved index h0 h2 h4 h5 h6 h7 h25]
    simp [NPOracleState.write, NPOracleState.jump, relocateState, hlow, hframe,
      h22, h23, h31, h50]

-- Ten request-building steps around the relocated address selector.
private theorem run_selectiveUniversalNodeAddressCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (result : SelectiveWire (descriptionWidth width bound))
    (rowBase start limit widthValue addressWord : ℕ)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveAddressSelectInput (selectiveStateCode state)
          (descriptionWidth width bound) rowBase start limit widthValue
          addressWord →
      runNPOracleProgram selectiveAddressSelectProgram maximumBits calleeFuel
          frame =
        some (selectiveWireCode result))
    (hrequestBits :
      natBitLength
          (selectiveAddressSelectInput (selectiveStateCode state)
            (descriptionWidth width bound) rowBase start limit widthValue
            addressWord) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (hpc : machine.pc = 97)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth width bound)
    (hrowBase : machine.registers 10 = rowBase)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hwidth : machine.registers 48 = widthValue)
    (haddress : machine.registers 49 = addressWord)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 119 →
      resumed.registers 0 = selectiveWireCode result →
      resumed.registers 2 = selectiveStateCode result.state →
      resumed.registers 4 = result.state.target - result.state.next →
      resumed.registers 6 = result.state.next →
      resumed.registers 7 = selectiveSelectedCode result.state.selected →
      resumed.registers 25 = result.output →
      (∀ index : ℕ, index < 1000 ∧ index ≠ 0 ∧ index ≠ 2 ∧ index ≠ 4 ∧
        index ≠ 5 ∧ index ≠ 6 ∧ index ≠ 7 ∧ index ≠ 22 ∧ index ≠ 23 ∧
        index ≠ 25 ∧ index ≠ 31 ∧ index ≠ 50 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (10 + (calleeFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveAddressSelectInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hfive := natBitLength_pair_right hfour
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  rw [show 10 + (calleeFuel + (7 + extraFuel)) =
    9 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalNodeProgram_controllerAt (pc := 97) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 9 + (calleeFuel + (7 + extraFuel)) =
    8 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalNodeProgram_controllerAt (pc := 98) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hremaining, hstateForm])
    hstateBits]
  rw [show 8 + (calleeFuel + (7 + extraFuel)) =
    7 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair widthValue addressWord)
    (selectiveUniversalNodeProgram_controllerAt (pc := 99) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth, haddress]) hfive]
  rw [show 7 + (calleeFuel + (7 + extraFuel)) =
    6 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair limit (Nat.pair widthValue addressWord))
    (selectiveUniversalNodeProgram_controllerAt (pc := 100) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit]) hfour]
  rw [show 6 + (calleeFuel + (7 + extraFuel)) =
    5 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair start (Nat.pair limit (Nat.pair widthValue addressWord)))
    (selectiveUniversalNodeProgram_controllerAt (pc := 101) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) hthree]
  rw [show 5 + (calleeFuel + (7 + extraFuel)) =
    4 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair rowBase
        (Nat.pair start (Nat.pair limit (Nat.pair widthValue addressWord))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 102) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htwo]
  rw [show 4 + (calleeFuel + (7 + extraFuel)) =
    3 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair rowBase
          (Nat.pair start (Nat.pair limit (Nat.pair widthValue addressWord)))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 103) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [show 3 + (calleeFuel + (7 + extraFuel)) =
    2 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveAddressSelectInput (selectiveStateCode state)
        (descriptionWidth width bound) rowBase start limit widthValue
        addressWord)
    (selectiveUniversalNodeProgram_controllerAt (pc := 104) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump,
        selectiveAddressSelectInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (7 + extraFuel)) =
    1 + (calleeFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 105) rfl) rfl hzeroBits]
  rw [show 1 + (calleeFuel + (7 + extraFuel)) =
    calleeFuel + (7 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 106) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := selectiveAddressSelectProgram)
    (calleeOutput := selectiveWireCode result)
    selectiveUniversalNodeProgram_addressCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine hcalleeRun frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    refine run_selectiveUniversalNodeReturn result maximumBits extraFuel
      finalOutput _ hwireBits (by simp [NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) ?_
    intro resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut hpreserved
    refine hcontinue resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut ?_
    intro index hind
    obtain ⟨hlt, h0, h2, h4, h5, h6, h7, h22, h23, h25, h31, h50⟩ := hind
    have hlow : ¬ (7000 ≤ index) := by omega
    have hframe : index ≠ 7000 := by omega
    rw [hpreserved index h0 h2 h4 h5 h6 h7 h25]
    simp [NPOracleState.write, NPOracleState.jump, relocateState, hlow, hframe,
      h22, h23, h31, h50]

-- Five request-building steps around the relocated append transition.
private theorem run_selectiveUniversalNodeEmitCall {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (node : BooleanNode (descriptionWidth width bound))
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode node)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode (state.emit node))) ≤
        maximumBits)
    (hpc : machine.pc = 107)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 21 = rawCircuitNodeCode node)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 119 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 2 = selectiveStateCode (state.emit node).state →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 25 = (state.emit node).output →
      (∀ index : ℕ, index < 1000 ∧ index ≠ 0 ∧ index ≠ 2 ∧ index ≠ 4 ∧
        index ≠ 5 ∧ index ≠ 6 ∧ index ≠ 7 ∧ index ≠ 22 ∧ index ≠ 23 ∧
        index ≠ 25 ∧ index ≠ 31 ∧ index ≠ 50 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hinputForm :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        Nat.pair (selectiveStateCode state) (rawCircuitNodeCode node) := rfl
  have hinputFlat := hinputBits
  rw [hinputForm] at hinputFlat
  have hstateBits := natBitLength_pair_left hinputFlat
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  have hwireFlat := natBitLength_pair_right hwireBits
  have hemitOutput :
      selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        selectiveWireCode (state.emit node) :=
    selectiveEmitOutput_eq_wireCode state node hordered
  have hemitCalleeBits :
      selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) ≤
        maximumBits := by
    unfold selectiveEmitBits selectiveEmitWorkBound
    rcases Nat.le_total
        (selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
        (selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
        with hle | hle
    · rw [max_eq_right hle, hemitOutput]
      exact hwireFlat
    · rw [max_eq_left hle]
      exact hinputBits
  rw [show 5 + (emitFuel + (7 + extraFuel)) =
    4 + (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUniversalNodeProgram_controllerAt (pc := 107) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    3 + (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUniversalNodeProgram_controllerAt (pc := 108) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hremaining, hstateForm])
    hstateBits]
  rw [show 3 + (emitFuel + (7 + extraFuel)) =
    2 + (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveUniversalNodeProgram_controllerAt (pc := 109) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    1 + (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 110) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    emitFuel + (7 + extraFuel) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 111) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveUniversalNodeProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state node hordered frame hframePc ?_)
      hemitCalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    refine run_selectiveUniversalNodeReturn (state.emit node) maximumBits
      extraFuel finalOutput _ hwireBits (by simp [NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) ?_
    intro resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut hpreserved
    refine hcontinue resumed hresumedPc hwire hstateOut hremainingOut hnextOut
      hselectedOut houtputOut ?_
    intro index hind
    obtain ⟨hlt, h0, h2, h4, h5, h6, h7, h22, h23, h25, _, h50⟩ := hind
    have hlow : ¬ (10000 ≤ index) := by omega
    have hframe : index ≠ 10000 := by omega
    rw [hpreserved index h0 h2 h4 h5 h6 h7 h25]
    simp [NPOracleState.write, NPOracleState.jump, relocateState, hlow, hframe,
      h22, h23, h50]

/-! ## 5. The phase dispatcher

Every call returns to the same block, so the controller records which phase it
was in and the dispatcher at `119` counts that phase down to route the return.
§5 proves one routing lemma per phase; each is a countdown of the phase
register against the eight fixed branch targets. -/

-- Phase 0 returns to the controller at `22`.
private theorem run_selectiveUniversalNodeDispatchZero
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 22 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (1 + extraFuel) machine =
      some finalOutput := by
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_pos hphase]
  refine hcontinue _ rfl ?_
  intro index _
  simp [NPOracleState.jump]

-- Phase 1 returns to the controller at `28`.
private theorem run_selectiveUniversalNodeDispatchOne
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 1)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 28 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (3 + extraFuel) machine =
      some finalOutput := by
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

-- Phase 2 returns to the controller at `34`.
private theorem run_selectiveUniversalNodeDispatchTwo
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 2)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 34 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (5 + extraFuel) machine =
      some finalOutput := by
  rw [show 5 + extraFuel = 4 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 4 + extraFuel = 3 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (1 : ℕ) ≤ 7)).trans hbits)]
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 122) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 123) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

-- Phase 3 returns to the controller at `39`.
private theorem run_selectiveUniversalNodeDispatchThree
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 3)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 39 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (7 + extraFuel) machine =
      some finalOutput := by
  rw [show 7 + extraFuel = 6 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 6 + extraFuel = 5 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 2)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (2 : ℕ) ≤ 7)).trans hbits)]
  rw [show 5 + extraFuel = 4 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 4 + extraFuel = 3 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveUniversalNodeProgram_controllerAt (pc := 122) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (1 : ℕ) ≤ 7)).trans hbits)]
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 123) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 124) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 125) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

-- Phase 4 returns to the controller at `45`.
private theorem run_selectiveUniversalNodeDispatchFour
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 4)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 45 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (9 + extraFuel) machine =
      some finalOutput := by
  rw [show 9 + extraFuel = 8 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 8 + extraFuel = 7 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 3)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (3 : ℕ) ≤ 7)).trans hbits)]
  rw [show 7 + extraFuel = 6 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 6 + extraFuel = 5 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 2)
    (selectiveUniversalNodeProgram_controllerAt (pc := 122) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (2 : ℕ) ≤ 7)).trans hbits)]
  rw [show 5 + extraFuel = 4 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 123) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 4 + extraFuel = 3 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveUniversalNodeProgram_controllerAt (pc := 124) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (1 : ℕ) ≤ 7)).trans hbits)]
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 125) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 126) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 127) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

-- Phase 5 returns to the controller at `53`.
private theorem run_selectiveUniversalNodeDispatchFive
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 5)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 53 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (11 + extraFuel) machine =
      some finalOutput := by
  rw [show 11 + extraFuel = 10 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 10 + extraFuel = 9 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 4)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (4 : ℕ) ≤ 7)).trans hbits)]
  rw [show 9 + extraFuel = 8 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 8 + extraFuel = 7 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 3)
    (selectiveUniversalNodeProgram_controllerAt (pc := 122) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (3 : ℕ) ≤ 7)).trans hbits)]
  rw [show 7 + extraFuel = 6 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 123) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 6 + extraFuel = 5 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 2)
    (selectiveUniversalNodeProgram_controllerAt (pc := 124) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (2 : ℕ) ≤ 7)).trans hbits)]
  rw [show 5 + extraFuel = 4 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 125) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 4 + extraFuel = 3 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveUniversalNodeProgram_controllerAt (pc := 126) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (1 : ℕ) ≤ 7)).trans hbits)]
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 127) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 128) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 129) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

-- Phase 6 returns to the controller at `61`.
private theorem run_selectiveUniversalNodeDispatchSix
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 6)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 61 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (13 + extraFuel) machine =
      some finalOutput := by
  rw [show 13 + extraFuel = 12 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 12 + extraFuel = 11 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 5)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (5 : ℕ) ≤ 7)).trans hbits)]
  rw [show 11 + extraFuel = 10 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 10 + extraFuel = 9 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 4)
    (selectiveUniversalNodeProgram_controllerAt (pc := 122) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (4 : ℕ) ≤ 7)).trans hbits)]
  rw [show 9 + extraFuel = 8 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 123) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 8 + extraFuel = 7 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 3)
    (selectiveUniversalNodeProgram_controllerAt (pc := 124) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (3 : ℕ) ≤ 7)).trans hbits)]
  rw [show 7 + extraFuel = 6 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 125) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 6 + extraFuel = 5 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 2)
    (selectiveUniversalNodeProgram_controllerAt (pc := 126) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (2 : ℕ) ≤ 7)).trans hbits)]
  rw [show 5 + extraFuel = 4 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 127) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 4 + extraFuel = 3 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveUniversalNodeProgram_controllerAt (pc := 128) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (1 : ℕ) ≤ 7)).trans hbits)]
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 129) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 130) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 131) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

-- Phase 7 returns to the controller at `78`.
private theorem run_selectiveUniversalNodeDispatchSeven
    {maximumBits extraFuel finalOutput : ℕ} (machine : NPOracleState)
    (hbits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 119)
    (hphase : machine.registers 30 = 7)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 78 →
      (∀ index : ℕ, index ≠ 30 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveUniversalNodeProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (15 + extraFuel) machine =
      some finalOutput := by
  rw [show 15 + extraFuel = 14 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 119) rfl) hpc]
  rw [if_neg (by rw [hphase]; omega)]
  rw [show 14 + extraFuel = 13 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 6)
    (selectiveUniversalNodeProgram_controllerAt (pc := 120) rfl) rfl
    (by simp [NPOracleState.jump, hphase])
    ((natBitLength_mono (by omega : (6 : ℕ) ≤ 7)).trans hbits)]
  rw [show 13 + extraFuel = 12 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 121) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 12 + extraFuel = 11 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 5)
    (selectiveUniversalNodeProgram_controllerAt (pc := 122) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (5 : ℕ) ≤ 7)).trans hbits)]
  rw [show 11 + extraFuel = 10 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 123) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 10 + extraFuel = 9 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 4)
    (selectiveUniversalNodeProgram_controllerAt (pc := 124) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (4 : ℕ) ≤ 7)).trans hbits)]
  rw [show 9 + extraFuel = 8 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 125) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 8 + extraFuel = 7 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 3)
    (selectiveUniversalNodeProgram_controllerAt (pc := 126) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (3 : ℕ) ≤ 7)).trans hbits)]
  rw [show 7 + extraFuel = 6 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 127) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 6 + extraFuel = 5 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 2)
    (selectiveUniversalNodeProgram_controllerAt (pc := 128) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (2 : ℕ) ≤ 7)).trans hbits)]
  rw [show 5 + extraFuel = 4 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 129) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 4 + extraFuel = 3 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 1)
    (selectiveUniversalNodeProgram_controllerAt (pc := 130) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (1 : ℕ) ≤ 7)).trans hbits)]
  rw [show 3 + extraFuel = 2 + extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 131) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [show 2 + extraFuel = 1 + extraFuel + 1 by omega]
  rw [run_decrement_instruction (value := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 132) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega : (0 : ℕ) ≤ 7)).trans hbits)]
  rw [show 1 + extraFuel = extraFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 133) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl ?_
  intro index h30
  simp [NPOracleState.write, NPOracleState.jump, h30]

/-! ## 6. The eight phases at the typed level

Each phase's call frame returns an abstract wire; the identities below name
those wires as the source compiler's own stages, so §7 can feed the level
premises straight into the trace. -/

private theorem universalNodeLeft_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ) :
    selectiveCompileFieldSelect state
        (fun candidate value =>
          unaryEqualsExpr candidate 6 (boundedCircuitFieldLimit width bound) value
            (universalNodeFirstBlock width bound)) row priorValues =
      universalNodeLeft state row priorValues := rfl

private theorem universalNodeRight_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ) :
    selectiveCompileFieldSelect (universalNodeLeft state row priorValues).state
        (fun candidate value =>
          unaryEqualsExpr candidate (6 + boundedCircuitFieldLimit width bound)
            (boundedCircuitFieldLimit width bound) value
            (universalNodeSecondBlock width bound)) row priorValues =
      universalNodeRight state row priorValues := rfl

private theorem universalNodeConstant_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (priorValues : List ℕ) :
    selectiveCompileExpr (universalNodeRight state row priorValues).state
        (unaryEqualsExpr (n := width) row 6 (boundedCircuitFieldLimit width bound) 1
          (universalNodeFirstBlock width bound)) =
      universalNodeConstant state row priorValues := rfl

private theorem universalNodeInputValue_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    selectiveCompileExpr (universalNodeConstant state row priorValues).state
        (constantAddressSelectionExpr row address) =
      universalNodeInputValue state row address priorValues := rfl

private theorem universalNodeNegated_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    (universalNodeInputValue state row address priorValues).state.emit
        (BooleanNode.not (universalNodeLeft state row priorValues).output) =
      universalNodeNegated state row address priorValues := rfl

private theorem universalNodeConjunction_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    (universalNodeNegated state row address priorValues).state.emit
        (BooleanNode.and (universalNodeLeft state row priorValues).output
          (universalNodeRight state row priorValues).output) =
      universalNodeConjunction state row address priorValues := rfl

private theorem universalNodeDisjunction_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    (universalNodeConjunction state row address priorValues).state.emit
        (BooleanNode.or (universalNodeLeft state row priorValues).output
          (universalNodeRight state row priorValues).output) =
      universalNodeDisjunction state row address priorValues := rfl

private theorem universalNodeResult_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    selectiveCompileFieldSelect (universalNodeDisjunction state row address priorValues).state
        (fun candidate value =>
          unaryEqualsExpr candidate 0 6 value
            (universalNodeTagBlock width bound)) row
        (universalNodeCases state row address priorValues) =
      selectiveCompileUniversalNode state row address priorValues := rfl

private theorem universalNodeCasesCode_eq {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width) (priorValues : List ℕ) :
    encodeTaggedList (universalNodeCases state row address priorValues) =
      Nat.pair 1 (Nat.pair (universalNodeConstant state row priorValues).output <|
        Nat.pair 1 (Nat.pair (universalNodeInputValue state row address priorValues).output <|
          Nat.pair 1 (Nat.pair (universalNodeNegated state row address priorValues).output <|
            Nat.pair 1 (Nat.pair (universalNodeConjunction state row address priorValues).output <|
              Nat.pair 1
                (Nat.pair
                  (universalNodeDisjunction state row address priorValues).output
                  0))))) := rfl

/-! ## 7. The whole 641-instruction stream

The controller is straight line: a sixteen-step request parser, the eight
phases through §4's call frames and §5's dispatchers, and the halt. -/

set_option maxHeartbeats 4000000 in
-- Sixteen parsing steps, eight phases, one halt.
private theorem run_selectiveUniversalNodeProgram_of_wires {width bound : ℕ}
    (state : SelectiveState (descriptionWidth width bound))
    (left right constantValue inputValue negated conjunction disjunction
      result : SelectiveWire (descriptionWidth width bound))
    (rowBase fieldLimit widthValue addressWord priorCode casesCode : ℕ)
    (maximumBits leftFuel rightFuel constantFuel addressFuel notFuel andFuel
      orFuel tagFuel : ℕ)
    (restZero restOne restTwo restThree restFour restFive restSix : ℕ)
    (hrestZero : restZero = leftFuel + restOne)
    (hrestOne : restOne = rightFuel + restTwo)
    (hrestTwo : restTwo = constantFuel + restThree)
    (hrestThree : restThree = addressFuel + restFour)
    (hrestFour : restFour = notFuel + restFive)
    (hrestFive : restFive = andFuel + restSix)
    (hrestSix : restSix = orFuel + tagFuel)
    (hnegated : inputValue.state.emit (BooleanNode.not left.output) = negated)
    (hconjunction :
      negated.state.emit (BooleanNode.and left.output right.output) =
        conjunction)
    (hdisjunction :
      conjunction.state.emit (BooleanNode.or left.output right.output) =
        disjunction)
    (hcasesCode :
      casesCode =
        Nat.pair 1 (Nat.pair constantValue.output <|
          Nat.pair 1 (Nat.pair inputValue.output <|
            Nat.pair 1 (Nat.pair negated.output <|
              Nat.pair 1 (Nat.pair conjunction.output <|
                Nat.pair 1 (Nat.pair disjunction.output 0))))))
    (hinputValueOrdered : selectiveStateOrdered inputValue.state)
    (hnegatedOrdered : selectiveStateOrdered negated.state)
    (hconjunctionOrdered : selectiveStateOrdered conjunction.state)
    (hnotFuel :
      notFuel =
        selectiveEmitFuel (inputValue.state.target - inputValue.state.next)
          (selectiveSelectedCode inputValue.state.selected))
    (handFuel :
      andFuel =
        selectiveEmitFuel (negated.state.target - negated.state.next)
          (selectiveSelectedCode negated.state.selected))
    (horFuel :
      orFuel =
        selectiveEmitFuel (conjunction.state.target - conjunction.state.next)
          (selectiveSelectedCode conjunction.state.selected))
    (hleftRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode state)
          (descriptionWidth width bound) rowBase 6 fieldLimit priorCode →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits leftFuel
          frame =
        some (selectiveWireCode left))
    (hrightRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode left.state)
          (descriptionWidth width bound) rowBase (6 + fieldLimit) fieldLimit
          priorCode →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits rightFuel
          frame =
        some (selectiveWireCode right))
    (hconstantRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveUnaryInput (selectiveStateCode right.state)
          (descriptionWidth width bound) rowBase 6 fieldLimit 1 →
      runNPOracleProgram selectiveUnaryProgram maximumBits constantFuel frame =
        some (selectiveWireCode constantValue))
    (haddressRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveAddressSelectInput (selectiveStateCode constantValue.state)
          (descriptionWidth width bound) rowBase 6 fieldLimit widthValue
          addressWord →
      runNPOracleProgram selectiveAddressSelectProgram maximumBits addressFuel
          frame =
        some (selectiveWireCode inputValue))
    (htagRun : ∀ frame : NPOracleState, frame.pc = 0 →
      frame.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode disjunction.state)
          (descriptionWidth width bound) rowBase 0 6 casesCode →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits tagFuel
          frame =
        some (selectiveWireCode result))
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUniversalNodeInput (selectiveStateCode state)
            (descriptionWidth width bound) rowBase fieldLimit widthValue
            addressWord priorCode) ≤
        maximumBits)
    (hleftRequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode state)
            (descriptionWidth width bound) rowBase 6 fieldLimit priorCode) ≤
        maximumBits)
    (hleftWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode left)) ≤ maximumBits)
    (hrightRequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode left.state)
            (descriptionWidth width bound) rowBase (6 + fieldLimit) fieldLimit
            priorCode) ≤
        maximumBits)
    (hrightWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode right)) ≤ maximumBits)
    (hconstantRequestBits :
      natBitLength
          (selectiveUnaryInput (selectiveStateCode right.state)
            (descriptionWidth width bound) rowBase 6 fieldLimit 1) ≤
        maximumBits)
    (hconstantWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode constantValue)) ≤
        maximumBits)
    (haddressRequestBits :
      natBitLength
          (selectiveAddressSelectInput (selectiveStateCode constantValue.state)
            (descriptionWidth width bound) rowBase 6 fieldLimit widthValue
            addressWord) ≤
        maximumBits)
    (haddressWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode inputValue)) ≤ maximumBits)
    (hnotInputBits :
      natBitLength
          (selectiveEmitInput (inputValue.state.target - inputValue.state.next)
            inputValue.state.next
            (selectiveSelectedCode inputValue.state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (BooleanNode.not left.output))) ≤
        maximumBits)
    (hnotWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode negated)) ≤ maximumBits)
    (handInputBits :
      natBitLength
          (selectiveEmitInput (negated.state.target - negated.state.next)
            negated.state.next (selectiveSelectedCode negated.state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (BooleanNode.and left.output right.output))) ≤
        maximumBits)
    (handWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode conjunction)) ≤ maximumBits)
    (horInputBits :
      natBitLength
          (selectiveEmitInput (conjunction.state.target - conjunction.state.next)
            conjunction.state.next
            (selectiveSelectedCode conjunction.state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (BooleanNode.or left.output right.output))) ≤
        maximumBits)
    (horWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode disjunction)) ≤ maximumBits)
    (htagRequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode disjunction.state)
            (descriptionWidth width bound) rowBase 0 6 casesCode) ≤
        maximumBits)
    (htagWireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode result)) ≤ maximumBits)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveUniversalNodeInput (selectiveStateCode state)
          (descriptionWidth width bound) rowBase fieldLimit widthValue
          addressWord priorCode) :
    runNPOracleProgram selectiveUniversalNodeProgram maximumBits
        (260 + restZero) entry =
      some (selectiveWireCode result) := by
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth width bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hconstBits : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have houtputOf : ∀ wire : SelectiveWire (descriptionWidth width bound),
      natBitLength (Nat.pair 0 (selectiveWireCode wire)) ≤ maximumBits →
      natBitLength wire.output ≤ maximumBits :=
    fun wire hwire => natBitLength_pair_right (natBitLength_pair_right hwire)
  have hflat := hrequestBits
  simp only [selectiveUniversalNodeInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have hrowBaseBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hfieldLimitBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hwidthBits := natBitLength_pair_left hfour
  have hfive := natBitLength_pair_right hfour
  have haddressBits := natBitLength_pair_left hfive
  have hpriorBits := natBitLength_pair_right hfive
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left hnextSelectedBits
  have hselectedBits := natBitLength_pair_right hnextSelectedBits
  have hrightFlat := hrightRequestBits
  simp only [selectiveFieldSelectInput] at hrightFlat
  have hrightStartBits :=
    natBitLength_pair_left
      (natBitLength_pair_right
        (natBitLength_pair_right (natBitLength_pair_right hrightFlat)))
  have hleftOutputBits := houtputOf _ hleftWireBits
  have hrightOutputBits := houtputOf _ hrightWireBits
  have hconstantOutputBits := houtputOf _ hconstantWireBits
  have haddressOutputBits := houtputOf _ haddressWireBits
  have hnotOutputBits := houtputOf _ hnotWireBits
  have handOutputBits := houtputOf _ handWireBits
  have horOutputBits := houtputOf _ horWireBits
  have hnotNodeBits := natBitLength_pair_right hnotInputBits
  have hnotChildBits := natBitLength_pair_right hnotNodeBits
  have handNodeBits := natBitLength_pair_right handInputBits
  have handChildrenBits := natBitLength_pair_right handNodeBits
  have handLeftBits := natBitLength_pair_left handChildrenBits
  have handRightBits := natBitLength_pair_right handChildrenBits
  have horNodeBits := natBitLength_pair_right horInputBits
  have horChildrenBits := natBitLength_pair_right horNodeBits
  have horLeftBits := natBitLength_pair_left horChildrenBits
  have horRightBits := natBitLength_pair_right horChildrenBits
  have htagFlat := htagRequestBits
  simp only [selectiveFieldSelectInput] at htagFlat
  have htagCodeBits :=
    natBitLength_pair_right
      (natBitLength_pair_right
        (natBitLength_pair_right
          (natBitLength_pair_right (natBitLength_pair_right htagFlat))))
  have htagValuesBits := htagCodeBits
  rw [hcasesCode] at htagValuesBits
  have htagConsFive := natBitLength_pair_right htagValuesBits
  have htagListFour := natBitLength_pair_right htagConsFive
  have htagConsFour := natBitLength_pair_right htagListFour
  have htagListThree := natBitLength_pair_right htagConsFour
  have htagConsThree := natBitLength_pair_right htagListThree
  have htagListTwo := natBitLength_pair_right htagConsThree
  have htagConsTwo := natBitLength_pair_right htagListTwo
  have htagListOne := natBitLength_pair_right htagConsTwo
  have htagConsOne := natBitLength_pair_right htagListOne
  rw [show 260 + restZero = 259 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveUniversalNodeProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, selectiveUniversalNodeInput])
    hstateBits]
  rw [show 259 + restZero = 258 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair (descriptionWidth width bound) <|
      Nat.pair rowBase <|
        Nat.pair fieldLimit <|
          Nat.pair widthValue (Nat.pair addressWord priorCode))
    (selectiveUniversalNodeProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveUniversalNodeInput])
    hone]
  rw [show 258 + restZero = 257 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveUniversalNodeProgram_controllerAt (pc := 2) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateForm state])
    hremainingBits]
  rw [show 257 + restZero = 256 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair state.next
      (selectiveSelectedCode state.selected))
    (selectiveUniversalNodeProgram_controllerAt (pc := 3) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateForm state])
    hnextSelectedBits]
  rw [show 256 + restZero = 255 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveUniversalNodeProgram_controllerAt (pc := 4) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hnextBits]
  rw [show 255 + restZero = 254 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveSelectedCode state.selected)
    (selectiveUniversalNodeProgram_controllerAt (pc := 5) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hselectedBits]
  rw [show 254 + restZero = 253 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := descriptionWidth width bound)
    (selectiveUniversalNodeProgram_controllerAt (pc := 6) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [show 253 + restZero = 252 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair rowBase <|
      Nat.pair fieldLimit <|
        Nat.pair widthValue (Nat.pair addressWord priorCode))
    (selectiveUniversalNodeProgram_controllerAt (pc := 7) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    htwo]
  rw [show 252 + restZero = 251 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowBase)
    (selectiveUniversalNodeProgram_controllerAt (pc := 8) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hrowBaseBits]
  rw [show 251 + restZero = 250 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair fieldLimit <|
      Nat.pair widthValue (Nat.pair addressWord priorCode))
    (selectiveUniversalNodeProgram_controllerAt (pc := 9) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hthree]
  rw [show 250 + restZero = 249 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := fieldLimit)
    (selectiveUniversalNodeProgram_controllerAt (pc := 10) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hfieldLimitBits]
  rw [show 249 + restZero = 248 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair widthValue (Nat.pair addressWord priorCode))
    (selectiveUniversalNodeProgram_controllerAt (pc := 11) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hfour]
  rw [show 248 + restZero = 247 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := widthValue)
    (selectiveUniversalNodeProgram_controllerAt (pc := 12) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hwidthBits]
  rw [show 247 + restZero = 246 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair addressWord priorCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 13) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hfive]
  rw [show 246 + restZero = 245 + restZero + 1 by omega]
  rw [run_unpairLeft_instruction (value := addressWord)
    (selectiveUniversalNodeProgram_controllerAt (pc := 14) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    haddressBits]
  rw [show 245 + restZero = 244 + restZero + 1 by omega]
  rw [run_unpairRight_instruction (value := priorCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 15) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hpriorBits]
  rw [show 244 + restZero = 243 + restZero + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 16) rfl) rfl
    (hconstBits 6 (by omega))]
  rw [show 243 + restZero = 242 + restZero + 1 by omega]
  rw [run_copy_instruction (value := 6)
    (selectiveUniversalNodeProgram_controllerAt (pc := 17) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (hconstBits 6 (by omega))]
  rw [show 242 + restZero = 241 + restZero + 1 by omega]
  rw [run_copy_instruction (value := fieldLimit)
    (selectiveUniversalNodeProgram_controllerAt (pc := 18) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hfieldLimitBits]
  rw [show 241 + restZero = 240 + restZero + 1 by omega]
  rw [run_copy_instruction (value := priorCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 19) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    hpriorBits]
  rw [show 240 + restZero = 239 + restZero + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 20) rfl) rfl
    (hconstBits 0 (by omega))]
  rw [show 239 + restZero = 238 + restZero + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 21) rfl) rfl]
  simp only [ite_self]
  rw [hrestZero]
  rw [show 238 + (leftFuel + restOne) =
    9 + (leftFuel + (7 + (1 + (221 + restOne)))) by omega]
  refine run_selectiveUniversalNodeFieldCall state left rowBase 6 fieldLimit
    priorCode maximumBits leftFuel _ _ _ hleftRun hleftRequestBits
    hleftWireBits rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeZero hnodeZeroPc hnodeZeroWire hnodeZeroState hnodeZeroRemaining
    hnodeZeroNext hnodeZeroSelected hnodeZeroOutput hnodeZeroPre
  refine run_selectiveUniversalNodeDispatchZero nodeZero hnodeZeroPc
    (by
      rw [hnodeZeroPre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepOne hstepOnePc hstepOnePre
  have hstepOne4 :
      stepOne.registers 4 = left.state.target - left.state.next := by
    rw [hstepOnePre 4 (by omega)]
    exact hnodeZeroRemaining
  have hstepOne6 :
      stepOne.registers 6 = left.state.next := by
    rw [hstepOnePre 6 (by omega)]
    exact hnodeZeroNext
  have hstepOne7 :
      stepOne.registers 7 = selectiveSelectedCode left.state.selected := by
    rw [hstepOnePre 7 (by omega)]
    exact hnodeZeroSelected
  have hstepOne25 :
      stepOne.registers 25 = left.output := by
    rw [hstepOnePre 25 (by omega)]
    exact hnodeZeroOutput
  have hstepOne8 :
      stepOne.registers 8 = descriptionWidth width bound := by
    rw [hstepOnePre 8 (by omega), hnodeZeroPre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepOne10 :
      stepOne.registers 10 = rowBase := by
    rw [hstepOnePre 10 (by omega), hnodeZeroPre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepOne16 :
      stepOne.registers 16 = priorCode := by
    rw [hstepOnePre 16 (by omega), hnodeZeroPre 16 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepOne20 :
      stepOne.registers 20 = 6 := by
    rw [hstepOnePre 20 (by omega), hnodeZeroPre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepOne47 :
      stepOne.registers 47 = fieldLimit := by
    rw [hstepOnePre 47 (by omega), hnodeZeroPre 47 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepOne48 :
      stepOne.registers 48 = widthValue := by
    rw [hstepOnePre 48 (by omega), hnodeZeroPre 48 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepOne49 :
      stepOne.registers 49 = addressWord := by
    rw [hstepOnePre 49 (by omega), hnodeZeroPre 49 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  rw [show 221 + restOne = 220 + restOne + 1 by omega]
  rw [run_copy_instruction (value := left.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 22) rfl) hstepOnePc
    hstepOne25
    hleftOutputBits]
  rw [show 220 + restOne = 219 + restOne + 1 by omega]
  rw [run_add_instruction (value := 6 + fieldLimit)
    (selectiveUniversalNodeProgram_controllerAt (pc := 23) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne20, hstepOne47])
    hrightStartBits]
  rw [show 219 + restOne = 218 + restOne + 1 by omega]
  rw [run_copy_instruction (value := fieldLimit)
    (selectiveUniversalNodeProgram_controllerAt (pc := 24) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne47])
    hfieldLimitBits]
  rw [show 218 + restOne = 217 + restOne + 1 by omega]
  rw [run_copy_instruction (value := priorCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 25) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne16])
    hpriorBits]
  rw [show 217 + restOne = 216 + restOne + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 26) rfl) rfl
    (hconstBits 1 (by omega))]
  rw [show 216 + restOne = 215 + restOne + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 27) rfl) rfl]
  simp only [ite_self]
  rw [hrestOne]
  rw [show 215 + (rightFuel + restTwo) =
    9 + (rightFuel + (7 + (3 + (196 + restTwo)))) by omega]
  refine run_selectiveUniversalNodeFieldCall left.state right rowBase
    (6 + fieldLimit) fieldLimit priorCode maximumBits rightFuel _ _ _
    hrightRun hrightRequestBits hrightWireBits rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne7])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne8])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepOne10])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeOne hnodeOnePc hnodeOneWire hnodeOneState hnodeOneRemaining
    hnodeOneNext hnodeOneSelected hnodeOneOutput hnodeOnePre
  refine run_selectiveUniversalNodeDispatchOne nodeOne hsevenBits hnodeOnePc
    (by
      rw [hnodeOnePre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepTwo hstepTwoPc hstepTwoPre
  have hstepTwo4 :
      stepTwo.registers 4 = right.state.target - right.state.next := by
    rw [hstepTwoPre 4 (by omega)]
    exact hnodeOneRemaining
  have hstepTwo6 :
      stepTwo.registers 6 = right.state.next := by
    rw [hstepTwoPre 6 (by omega)]
    exact hnodeOneNext
  have hstepTwo7 :
      stepTwo.registers 7 = selectiveSelectedCode right.state.selected := by
    rw [hstepTwoPre 7 (by omega)]
    exact hnodeOneSelected
  have hstepTwo25 :
      stepTwo.registers 25 = right.output := by
    rw [hstepTwoPre 25 (by omega)]
    exact hnodeOneOutput
  have hstepTwo8 :
      stepTwo.registers 8 = descriptionWidth width bound := by
    rw [hstepTwoPre 8 (by omega), hnodeOnePre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepOne8]
  have hstepTwo10 :
      stepTwo.registers 10 = rowBase := by
    rw [hstepTwoPre 10 (by omega), hnodeOnePre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepOne10]
  have hstepTwo20 :
      stepTwo.registers 20 = 6 := by
    rw [hstepTwoPre 20 (by omega), hnodeOnePre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepOne20]
  have hstepTwo40 :
      stepTwo.registers 40 = left.output := by
    rw [hstepTwoPre 40 (by omega), hnodeOnePre 40 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepTwo47 :
      stepTwo.registers 47 = fieldLimit := by
    rw [hstepTwoPre 47 (by omega), hnodeOnePre 47 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepOne47]
  have hstepTwo48 :
      stepTwo.registers 48 = widthValue := by
    rw [hstepTwoPre 48 (by omega), hnodeOnePre 48 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepOne48]
  have hstepTwo49 :
      stepTwo.registers 49 = addressWord := by
    rw [hstepTwoPre 49 (by omega), hnodeOnePre 49 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepOne49]
  rw [show 196 + restTwo = 195 + restTwo + 1 by omega]
  rw [run_copy_instruction (value := right.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 28) rfl) hstepTwoPc
    hstepTwo25
    hrightOutputBits]
  rw [show 195 + restTwo = 194 + restTwo + 1 by omega]
  rw [run_copy_instruction (value := 6)
    (selectiveUniversalNodeProgram_controllerAt (pc := 29) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo20])
    (hconstBits 6 (by omega))]
  rw [show 194 + restTwo = 193 + restTwo + 1 by omega]
  rw [run_copy_instruction (value := fieldLimit)
    (selectiveUniversalNodeProgram_controllerAt (pc := 30) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo47])
    hfieldLimitBits]
  rw [show 193 + restTwo = 192 + restTwo + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 31) rfl) rfl
    (hconstBits 1 (by omega))]
  rw [show 192 + restTwo = 191 + restTwo + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 32) rfl) rfl
    (hconstBits 2 (by omega))]
  rw [show 191 + restTwo = 190 + restTwo + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 33) rfl) rfl]
  simp only [ite_self]
  rw [hrestTwo]
  rw [show 190 + (constantFuel + restThree) =
    9 + (constantFuel + (7 + (5 + (169 + restThree)))) by omega]
  refine run_selectiveUniversalNodeUnaryCall right.state constantValue rowBase
    6 fieldLimit 1 maximumBits constantFuel _ _ _ hconstantRun
    hconstantRequestBits hconstantWireBits rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo7])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo8])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepTwo10])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeTwo hnodeTwoPc hnodeTwoWire hnodeTwoState hnodeTwoRemaining
    hnodeTwoNext hnodeTwoSelected hnodeTwoOutput hnodeTwoPre
  refine run_selectiveUniversalNodeDispatchTwo nodeTwo hsevenBits hnodeTwoPc
    (by
      rw [hnodeTwoPre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepThree hstepThreePc hstepThreePre
  have hstepThree4 :
      stepThree.registers 4 = constantValue.state.target - constantValue.state.next := by
    rw [hstepThreePre 4 (by omega)]
    exact hnodeTwoRemaining
  have hstepThree6 :
      stepThree.registers 6 = constantValue.state.next := by
    rw [hstepThreePre 6 (by omega)]
    exact hnodeTwoNext
  have hstepThree7 :
      stepThree.registers 7 = selectiveSelectedCode constantValue.state.selected := by
    rw [hstepThreePre 7 (by omega)]
    exact hnodeTwoSelected
  have hstepThree25 :
      stepThree.registers 25 = constantValue.output := by
    rw [hstepThreePre 25 (by omega)]
    exact hnodeTwoOutput
  have hstepThree8 :
      stepThree.registers 8 = descriptionWidth width bound := by
    rw [hstepThreePre 8 (by omega), hnodeTwoPre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo8]
  have hstepThree10 :
      stepThree.registers 10 = rowBase := by
    rw [hstepThreePre 10 (by omega), hnodeTwoPre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo10]
  have hstepThree20 :
      stepThree.registers 20 = 6 := by
    rw [hstepThreePre 20 (by omega), hnodeTwoPre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo20]
  have hstepThree40 :
      stepThree.registers 40 = left.output := by
    rw [hstepThreePre 40 (by omega), hnodeTwoPre 40 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo40]
  have hstepThree41 :
      stepThree.registers 41 = right.output := by
    rw [hstepThreePre 41 (by omega), hnodeTwoPre 41 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  have hstepThree47 :
      stepThree.registers 47 = fieldLimit := by
    rw [hstepThreePre 47 (by omega), hnodeTwoPre 47 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo47]
  have hstepThree48 :
      stepThree.registers 48 = widthValue := by
    rw [hstepThreePre 48 (by omega), hnodeTwoPre 48 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo48]
  have hstepThree49 :
      stepThree.registers 49 = addressWord := by
    rw [hstepThreePre 49 (by omega), hnodeTwoPre 49 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepTwo49]
  rw [show 169 + restThree = 168 + restThree + 1 by omega]
  rw [run_copy_instruction (value := constantValue.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 34) rfl) hstepThreePc
    hstepThree25
    hconstantOutputBits]
  rw [show 168 + restThree = 167 + restThree + 1 by omega]
  rw [run_copy_instruction (value := 6)
    (selectiveUniversalNodeProgram_controllerAt (pc := 35) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree20])
    (hconstBits 6 (by omega))]
  rw [show 167 + restThree = 166 + restThree + 1 by omega]
  rw [run_copy_instruction (value := fieldLimit)
    (selectiveUniversalNodeProgram_controllerAt (pc := 36) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree47])
    hfieldLimitBits]
  rw [show 166 + restThree = 165 + restThree + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 37) rfl) rfl
    (hconstBits 3 (by omega))]
  rw [show 165 + restThree = 164 + restThree + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 38) rfl) rfl]
  simp only [ite_self]
  rw [hrestThree]
  rw [show 164 + (addressFuel + restFour) =
    10 + (addressFuel + (7 + (7 + (140 + restFour)))) by omega]
  refine run_selectiveUniversalNodeAddressCall constantValue.state inputValue
    rowBase 6 fieldLimit widthValue addressWord maximumBits addressFuel _ _ _
    haddressRun haddressRequestBits haddressWireBits rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree7])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree8])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree10])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree48])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepThree49])
    ?_
  intro nodeThree hnodeThreePc hnodeThreeWire hnodeThreeState hnodeThreeRemaining
    hnodeThreeNext hnodeThreeSelected hnodeThreeOutput hnodeThreePre
  refine run_selectiveUniversalNodeDispatchThree nodeThree hsevenBits hnodeThreePc
    (by
      rw [hnodeThreePre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepFour hstepFourPc hstepFourPre
  have hstepFour4 :
      stepFour.registers 4 = inputValue.state.target - inputValue.state.next := by
    rw [hstepFourPre 4 (by omega)]
    exact hnodeThreeRemaining
  have hstepFour6 :
      stepFour.registers 6 = inputValue.state.next := by
    rw [hstepFourPre 6 (by omega)]
    exact hnodeThreeNext
  have hstepFour7 :
      stepFour.registers 7 = selectiveSelectedCode inputValue.state.selected := by
    rw [hstepFourPre 7 (by omega)]
    exact hnodeThreeSelected
  have hstepFour25 :
      stepFour.registers 25 = inputValue.output := by
    rw [hstepFourPre 25 (by omega)]
    exact hnodeThreeOutput
  have hstepFour8 :
      stepFour.registers 8 = descriptionWidth width bound := by
    rw [hstepFourPre 8 (by omega), hnodeThreePre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepThree8]
  have hstepFour10 :
      stepFour.registers 10 = rowBase := by
    rw [hstepFourPre 10 (by omega), hnodeThreePre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepThree10]
  have hstepFour20 :
      stepFour.registers 20 = 6 := by
    rw [hstepFourPre 20 (by omega), hnodeThreePre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepThree20]
  have hstepFour40 :
      stepFour.registers 40 = left.output := by
    rw [hstepFourPre 40 (by omega), hnodeThreePre 40 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepThree40]
  have hstepFour41 :
      stepFour.registers 41 = right.output := by
    rw [hstepFourPre 41 (by omega), hnodeThreePre 41 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepThree41]
  have hstepFour42 :
      stepFour.registers 42 = constantValue.output := by
    rw [hstepFourPre 42 (by omega), hnodeThreePre 42 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  rw [show 140 + restFour = 139 + restFour + 1 by omega]
  rw [run_copy_instruction (value := inputValue.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 39) rfl) hstepFourPc
    hstepFour25
    haddressOutputBits]
  rw [show 139 + restFour = 138 + restFour + 1 by omega]
  rw [run_add_instruction (value := descriptionWidth width bound + left.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 40) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFour8, hstepFour40])
    hnotChildBits]
  rw [show 138 + restFour = 137 + restFour + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 41) rfl) rfl
    (hconstBits 2 (by omega))]
  rw [show 137 + restFour = 136 + restFour + 1 by omega]
  rw [run_pair_instruction (value := rawCircuitNodeCode (n := descriptionWidth width bound)
      (BooleanNode.not left.output))
    (selectiveUniversalNodeProgram_controllerAt (pc := 42) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rawCircuitNodeCode])
    hnotNodeBits]
  rw [show 136 + restFour = 135 + restFour + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 43) rfl) rfl
    (hconstBits 4 (by omega))]
  rw [show 135 + restFour = 134 + restFour + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 44) rfl) rfl]
  simp only [ite_self]
  rw [hrestFour]
  rw [show 134 + (notFuel + restFive) =
    5 + (notFuel + (7 + (9 + (113 + restFive)))) by omega]
  refine run_selectiveUniversalNodeEmitCall inputValue.state
    (BooleanNode.not left.output) hinputValueOrdered maximumBits notFuel _ _ _
    hnotFuel hnotInputBits (by rw [hnegated]; exact hnotWireBits) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFour4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFour6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFour7])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeFour hnodeFourPc hnodeFourWire hnodeFourState hnodeFourRemaining
    hnodeFourNext hnodeFourSelected hnodeFourOutput hnodeFourPre
  rw [hnegated] at hnodeFourWire hnodeFourState hnodeFourRemaining
  rw [hnegated] at hnodeFourNext hnodeFourSelected hnodeFourOutput
  refine run_selectiveUniversalNodeDispatchFour nodeFour hsevenBits hnodeFourPc
    (by
      rw [hnodeFourPre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepFive hstepFivePc hstepFivePre
  have hstepFive4 :
      stepFive.registers 4 = negated.state.target - negated.state.next := by
    rw [hstepFivePre 4 (by omega)]
    exact hnodeFourRemaining
  have hstepFive6 :
      stepFive.registers 6 = negated.state.next := by
    rw [hstepFivePre 6 (by omega)]
    exact hnodeFourNext
  have hstepFive7 :
      stepFive.registers 7 = selectiveSelectedCode negated.state.selected := by
    rw [hstepFivePre 7 (by omega)]
    exact hnodeFourSelected
  have hstepFive25 :
      stepFive.registers 25 = negated.output := by
    rw [hstepFivePre 25 (by omega)]
    exact hnodeFourOutput
  have hstepFive8 :
      stepFive.registers 8 = descriptionWidth width bound := by
    rw [hstepFivePre 8 (by omega), hnodeFourPre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFour8]
  have hstepFive10 :
      stepFive.registers 10 = rowBase := by
    rw [hstepFivePre 10 (by omega), hnodeFourPre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFour10]
  have hstepFive20 :
      stepFive.registers 20 = 6 := by
    rw [hstepFivePre 20 (by omega), hnodeFourPre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFour20]
  have hstepFive40 :
      stepFive.registers 40 = left.output := by
    rw [hstepFivePre 40 (by omega), hnodeFourPre 40 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFour40]
  have hstepFive41 :
      stepFive.registers 41 = right.output := by
    rw [hstepFivePre 41 (by omega), hnodeFourPre 41 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFour41]
  have hstepFive42 :
      stepFive.registers 42 = constantValue.output := by
    rw [hstepFivePre 42 (by omega), hnodeFourPre 42 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFour42]
  have hstepFive43 :
      stepFive.registers 43 = inputValue.output := by
    rw [hstepFivePre 43 (by omega), hnodeFourPre 43 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  rw [show 113 + restFive = 112 + restFive + 1 by omega]
  rw [run_copy_instruction (value := negated.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 45) rfl) hstepFivePc
    hstepFive25
    hnotOutputBits]
  rw [show 112 + restFive = 111 + restFive + 1 by omega]
  rw [run_add_instruction (value := descriptionWidth width bound + left.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 46) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFive8, hstepFive40])
    handLeftBits]
  rw [show 111 + restFive = 110 + restFive + 1 by omega]
  rw [run_add_instruction (value := descriptionWidth width bound + right.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 47) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFive8, hstepFive41])
    handRightBits]
  rw [show 110 + restFive = 109 + restFive + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (descriptionWidth width bound + left.output)
      (descriptionWidth width bound + right.output))
    (selectiveUniversalNodeProgram_controllerAt (pc := 48) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    handChildrenBits]
  rw [show 109 + restFive = 108 + restFive + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 49) rfl) rfl
    (hconstBits 3 (by omega))]
  rw [show 108 + restFive = 107 + restFive + 1 by omega]
  rw [run_pair_instruction (value := rawCircuitNodeCode (n := descriptionWidth width bound)
      (BooleanNode.and left.output right.output))
    (selectiveUniversalNodeProgram_controllerAt (pc := 50) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rawCircuitNodeCode])
    handNodeBits]
  rw [show 107 + restFive = 106 + restFive + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 51) rfl) rfl
    (hconstBits 5 (by omega))]
  rw [show 106 + restFive = 105 + restFive + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 52) rfl) rfl]
  simp only [ite_self]
  rw [hrestFive]
  rw [show 105 + (andFuel + restSix) =
    5 + (andFuel + (7 + (11 + (82 + restSix)))) by omega]
  refine run_selectiveUniversalNodeEmitCall negated.state
    (BooleanNode.and left.output right.output) hnegatedOrdered maximumBits
    andFuel _ _ _ handFuel handInputBits
    (by rw [hconjunction]; exact handWireBits) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFive4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFive6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepFive7])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeFive hnodeFivePc hnodeFiveWire hnodeFiveState hnodeFiveRemaining
    hnodeFiveNext hnodeFiveSelected hnodeFiveOutput hnodeFivePre
  rw [hconjunction] at hnodeFiveWire hnodeFiveState hnodeFiveRemaining
  rw [hconjunction] at hnodeFiveNext hnodeFiveSelected hnodeFiveOutput
  refine run_selectiveUniversalNodeDispatchFive nodeFive hsevenBits hnodeFivePc
    (by
      rw [hnodeFivePre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepSix hstepSixPc hstepSixPre
  have hstepSix4 :
      stepSix.registers 4 = conjunction.state.target - conjunction.state.next := by
    rw [hstepSixPre 4 (by omega)]
    exact hnodeFiveRemaining
  have hstepSix6 :
      stepSix.registers 6 = conjunction.state.next := by
    rw [hstepSixPre 6 (by omega)]
    exact hnodeFiveNext
  have hstepSix7 :
      stepSix.registers 7 = selectiveSelectedCode conjunction.state.selected := by
    rw [hstepSixPre 7 (by omega)]
    exact hnodeFiveSelected
  have hstepSix25 :
      stepSix.registers 25 = conjunction.output := by
    rw [hstepSixPre 25 (by omega)]
    exact hnodeFiveOutput
  have hstepSix8 :
      stepSix.registers 8 = descriptionWidth width bound := by
    rw [hstepSixPre 8 (by omega), hnodeFivePre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive8]
  have hstepSix10 :
      stepSix.registers 10 = rowBase := by
    rw [hstepSixPre 10 (by omega), hnodeFivePre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive10]
  have hstepSix20 :
      stepSix.registers 20 = 6 := by
    rw [hstepSixPre 20 (by omega), hnodeFivePre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive20]
  have hstepSix40 :
      stepSix.registers 40 = left.output := by
    rw [hstepSixPre 40 (by omega), hnodeFivePre 40 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive40]
  have hstepSix41 :
      stepSix.registers 41 = right.output := by
    rw [hstepSixPre 41 (by omega), hnodeFivePre 41 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive41]
  have hstepSix42 :
      stepSix.registers 42 = constantValue.output := by
    rw [hstepSixPre 42 (by omega), hnodeFivePre 42 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive42]
  have hstepSix43 :
      stepSix.registers 43 = inputValue.output := by
    rw [hstepSixPre 43 (by omega), hnodeFivePre 43 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepFive43]
  have hstepSix44 :
      stepSix.registers 44 = negated.output := by
    rw [hstepSixPre 44 (by omega), hnodeFivePre 44 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  rw [show 82 + restSix = 81 + restSix + 1 by omega]
  rw [run_copy_instruction (value := conjunction.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 53) rfl) hstepSixPc
    hstepSix25
    handOutputBits]
  rw [show 81 + restSix = 80 + restSix + 1 by omega]
  rw [run_add_instruction (value := descriptionWidth width bound + left.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 54) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSix8, hstepSix40])
    horLeftBits]
  rw [show 80 + restSix = 79 + restSix + 1 by omega]
  rw [run_add_instruction (value := descriptionWidth width bound + right.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 55) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSix8, hstepSix41])
    horRightBits]
  rw [show 79 + restSix = 78 + restSix + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (descriptionWidth width bound + left.output)
      (descriptionWidth width bound + right.output))
    (selectiveUniversalNodeProgram_controllerAt (pc := 56) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    horChildrenBits]
  rw [show 78 + restSix = 77 + restSix + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 57) rfl) rfl
    (hconstBits 4 (by omega))]
  rw [show 77 + restSix = 76 + restSix + 1 by omega]
  rw [run_pair_instruction (value := rawCircuitNodeCode (n := descriptionWidth width bound)
      (BooleanNode.or left.output right.output))
    (selectiveUniversalNodeProgram_controllerAt (pc := 58) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, rawCircuitNodeCode])
    horNodeBits]
  rw [show 76 + restSix = 75 + restSix + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 59) rfl) rfl
    (hconstBits 6 (by omega))]
  rw [show 75 + restSix = 74 + restSix + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 60) rfl) rfl]
  simp only [ite_self]
  rw [hrestSix]
  rw [show 74 + (orFuel + tagFuel) =
    5 + (orFuel + (7 + (13 + (49 + tagFuel)))) by omega]
  refine run_selectiveUniversalNodeEmitCall conjunction.state
    (BooleanNode.or left.output right.output) hconjunctionOrdered maximumBits
    orFuel _ _ _ horFuel horInputBits
    (by rw [hdisjunction]; exact horWireBits) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSix4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSix6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSix7])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeSix hnodeSixPc hnodeSixWire hnodeSixState hnodeSixRemaining
    hnodeSixNext hnodeSixSelected hnodeSixOutput hnodeSixPre
  rw [hdisjunction] at hnodeSixWire hnodeSixState hnodeSixRemaining
  rw [hdisjunction] at hnodeSixNext hnodeSixSelected hnodeSixOutput
  refine run_selectiveUniversalNodeDispatchSix nodeSix hsevenBits hnodeSixPc
    (by
      rw [hnodeSixPre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepSeven hstepSevenPc hstepSevenPre
  have hstepSeven4 :
      stepSeven.registers 4 = disjunction.state.target - disjunction.state.next := by
    rw [hstepSevenPre 4 (by omega)]
    exact hnodeSixRemaining
  have hstepSeven6 :
      stepSeven.registers 6 = disjunction.state.next := by
    rw [hstepSevenPre 6 (by omega)]
    exact hnodeSixNext
  have hstepSeven7 :
      stepSeven.registers 7 = selectiveSelectedCode disjunction.state.selected := by
    rw [hstepSevenPre 7 (by omega)]
    exact hnodeSixSelected
  have hstepSeven25 :
      stepSeven.registers 25 = disjunction.output := by
    rw [hstepSevenPre 25 (by omega)]
    exact hnodeSixOutput
  have hstepSeven8 :
      stepSeven.registers 8 = descriptionWidth width bound := by
    rw [hstepSevenPre 8 (by omega), hnodeSixPre 8 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepSix8]
  have hstepSeven10 :
      stepSeven.registers 10 = rowBase := by
    rw [hstepSevenPre 10 (by omega), hnodeSixPre 10 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepSix10]
  have hstepSeven20 :
      stepSeven.registers 20 = 6 := by
    rw [hstepSevenPre 20 (by omega), hnodeSixPre 20 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepSix20]
  have hstepSeven42 :
      stepSeven.registers 42 = constantValue.output := by
    rw [hstepSevenPre 42 (by omega), hnodeSixPre 42 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepSix42]
  have hstepSeven43 :
      stepSeven.registers 43 = inputValue.output := by
    rw [hstepSevenPre 43 (by omega), hnodeSixPre 43 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepSix43]
  have hstepSeven44 :
      stepSeven.registers 44 = negated.output := by
    rw [hstepSevenPre 44 (by omega), hnodeSixPre 44 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hstepSix44]
  have hstepSeven45 :
      stepSeven.registers 45 = conjunction.output := by
    rw [hstepSevenPre 45 (by omega), hnodeSixPre 45 (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  rw [show 49 + tagFuel = 48 + tagFuel + 1 by omega]
  rw [run_copy_instruction (value := disjunction.output)
    (selectiveUniversalNodeProgram_controllerAt (pc := 61) rfl) hstepSevenPc
    hstepSeven25
    horOutputBits]
  rw [show 48 + tagFuel = 47 + tagFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 62) rfl) rfl
    (hconstBits 0 (by omega))]
  rw [show 47 + tagFuel = 46 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair disjunction.output 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 63) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    htagConsOne]
  rw [show 46 + tagFuel = 45 + tagFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 64) rfl) rfl
    (hconstBits 1 (by omega))]
  rw [show 45 + tagFuel = 44 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 (Nat.pair disjunction.output 0))
    (selectiveUniversalNodeProgram_controllerAt (pc := 65) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    htagListOne]
  rw [show 44 + tagFuel = 43 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair conjunction.output
      (Nat.pair 1 (Nat.pair disjunction.output 0)))
    (selectiveUniversalNodeProgram_controllerAt (pc := 66) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven45])
    htagConsTwo]
  rw [show 43 + tagFuel = 42 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 (Nat.pair conjunction.output
      (Nat.pair 1 (Nat.pair disjunction.output 0))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 67) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    htagListTwo]
  rw [show 42 + tagFuel = 41 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair negated.output <|
      Nat.pair 1 (Nat.pair conjunction.output
        (Nat.pair 1 (Nat.pair disjunction.output 0))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 68) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven44])
    htagConsThree]
  rw [show 41 + tagFuel = 40 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 <| Nat.pair negated.output <|
      Nat.pair 1 (Nat.pair conjunction.output
        (Nat.pair 1 (Nat.pair disjunction.output 0))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 69) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    htagListThree]
  rw [show 40 + tagFuel = 39 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair inputValue.output <| Nat.pair 1 <|
      Nat.pair negated.output <|
        Nat.pair 1 (Nat.pair conjunction.output
          (Nat.pair 1 (Nat.pair disjunction.output 0))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 70) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven43])
    htagConsFour]
  rw [show 39 + tagFuel = 38 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair 1 <| Nat.pair inputValue.output <| Nat.pair 1 <|
      Nat.pair negated.output <|
        Nat.pair 1 (Nat.pair conjunction.output
          (Nat.pair 1 (Nat.pair disjunction.output 0))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 71) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    htagListFour]
  rw [show 38 + tagFuel = 37 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair constantValue.output <| Nat.pair 1 <|
      Nat.pair inputValue.output <| Nat.pair 1 <|
        Nat.pair negated.output <|
          Nat.pair 1 (Nat.pair conjunction.output
            (Nat.pair 1 (Nat.pair disjunction.output 0))))
    (selectiveUniversalNodeProgram_controllerAt (pc := 72) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven42])
    htagConsFive]
  rw [show 37 + tagFuel = 36 + tagFuel + 1 by omega]
  rw [run_pair_instruction (value := casesCode)
    (selectiveUniversalNodeProgram_controllerAt (pc := 73) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hcasesCode])
    htagCodeBits]
  rw [show 36 + tagFuel = 35 + tagFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 74) rfl) rfl
    (hconstBits 0 (by omega))]
  rw [show 35 + tagFuel = 34 + tagFuel + 1 by omega]
  rw [run_copy_instruction (value := 6)
    (selectiveUniversalNodeProgram_controllerAt (pc := 75) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven20])
    (hconstBits 6 (by omega))]
  rw [show 34 + tagFuel = 33 + tagFuel + 1 by omega]
  rw [run_set_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 76) rfl) rfl
    hsevenBits]
  rw [show 33 + tagFuel = 32 + tagFuel + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUniversalNodeProgram_controllerAt (pc := 77) rfl) rfl]
  simp only [ite_self]
  rw [show 32 + tagFuel = 9 + (tagFuel + (7 + (15 + 1))) by omega]
  refine run_selectiveUniversalNodeFieldCall disjunction.state result rowBase 0
    6 casesCode maximumBits tagFuel _ _ _ htagRun htagRequestBits htagWireBits
    rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven4])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven6])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven7])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven8])
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstepSeven10])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    (by
      simp [NPOracleState.write, NPOracleState.jump])
    ?_
  intro nodeSeven hnodeSevenPc hnodeSevenWire hnodeSevenState hnodeSevenRemaining
    hnodeSevenNext hnodeSevenSelected hnodeSevenOutput hnodeSevenPre
  refine run_selectiveUniversalNodeDispatchSeven nodeSeven hsevenBits hnodeSevenPc
    (by
      rw [hnodeSevenPre 30 (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro stepEight hstepEightPc hstepEightPre
  refine run_halt_instruction (fuel := 0)
    (selectiveUniversalNodeProgram_controllerAt (pc := 78) rfl) hstepEightPc ?_
    (natBitLength_pair_right htagWireBits)
  rw [hstepEightPre 0 (by omega)]
  exact hnodeSevenWire

/-- **Level premise.**  The universal-evaluator row compiler compiles one
described DAG row at its own ABI frame, at an arbitrary entry state. -/
structure SelectiveUniversalNodeRunner (width bound : ℕ) where
  bits : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    BitInput width → List ℕ → ℕ
  fuel : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    BitInput width → List ℕ → ℕ
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (row : Fin (bound + 1)) (address : BitInput width)
      (priorValues : List ℕ), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveUniversalNodeInput (selectiveStateCode state)
        (descriptionWidth width bound) (row.val * rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width (encodeBitInput address)
        (encodeTaggedList priorValues) →
    runNPOracleProgram selectiveUniversalNodeProgram
        (bits state row address priorValues)
        (fuel state row address priorValues) entry =
      some
        (selectiveWireCode
          (selectiveCompileUniversalNode state row address priorValues))

/-- Every value one universal-evaluator row compilation writes, apart from the
values its own callees bound. -/
private def universalNodeBitsTerms {width bound : ℕ}
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (addressRunner : SelectiveAddressSelectRunner width bound)
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width)
    (priorValues : List ℕ) : List ℕ :=
  [ natBitLength 7
  , natBitLength (selectiveUniversalNodeInput (selectiveStateCode state) (descriptionWidth width
      bound) (row.val * rowWidth width bound) (boundedCircuitFieldLimit width bound) width
      (encodeBitInput address) (encodeTaggedList priorValues))
  , natBitLength (selectiveFieldSelectInput (selectiveStateCode state) (descriptionWidth width
      bound) (row.val * rowWidth width bound) 6 (boundedCircuitFieldLimit width bound)
      (encodeTaggedList priorValues))
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeLeft state row priorValues)))
  , fieldRunner.bits state row 6 (boundedCircuitFieldLimit width bound) (universalNodeFirstBlock
      width bound) priorValues
  , natBitLength (selectiveFieldSelectInput (selectiveStateCode (universalNodeLeft state row
      priorValues).state) (descriptionWidth width bound) (row.val * rowWidth width bound) (6 +
      (boundedCircuitFieldLimit width bound)) (boundedCircuitFieldLimit width bound)
      (encodeTaggedList priorValues))
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeRight state row priorValues)))
  , fieldRunner.bits (universalNodeLeft state row priorValues).state row (6 +
      (boundedCircuitFieldLimit width bound)) (boundedCircuitFieldLimit width bound)
      (universalNodeSecondBlock width bound) priorValues
  , natBitLength (selectiveUnaryInput (selectiveStateCode (universalNodeRight state row
      priorValues).state) (descriptionWidth width bound) (row.val * rowWidth width bound) 6
      (boundedCircuitFieldLimit width bound) 1)
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeConstant state row priorValues)))
  , selectiveUnaryRunBits (universalNodeRight state row priorValues).state
      (selectiveUnaryEqualsLiterals (n := width) row 6 (boundedCircuitFieldLimit width bound) 1
      (universalNodeFirstBlock width bound)) (row.val * rowWidth width bound) 6 1
  , natBitLength (selectiveAddressSelectInput (selectiveStateCode (universalNodeConstant state row
      priorValues).state) (descriptionWidth width bound) (row.val * rowWidth width bound) 6
      (boundedCircuitFieldLimit width bound) width (encodeBitInput address))
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeInputValue state row address
      priorValues)))
  , addressRunner.bits (universalNodeConstant state row priorValues).state row address
  , natBitLength (selectiveEmitInput ((universalNodeInputValue state row address
      priorValues).state.target - (universalNodeInputValue state row address
      priorValues).state.next) (universalNodeInputValue state row address priorValues).state.next
      (selectiveSelectedCode (universalNodeInputValue state row address
      priorValues).state.selected) (rawCircuitNodeCode (n := descriptionWidth width bound)
      (BooleanNode.not (universalNodeLeft state row priorValues).output)))
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeNegated state row address
      priorValues)))
  , natBitLength (selectiveEmitInput ((universalNodeNegated state row address
      priorValues).state.target - (universalNodeNegated state row address priorValues).state.next)
      (universalNodeNegated state row address priorValues).state.next (selectiveSelectedCode
      (universalNodeNegated state row address priorValues).state.selected) (rawCircuitNodeCode (n
      := descriptionWidth width bound) (BooleanNode.and (universalNodeLeft state row
      priorValues).output (universalNodeRight state row priorValues).output)))
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeConjunction state row address
      priorValues)))
  , natBitLength (selectiveEmitInput ((universalNodeConjunction state row address
      priorValues).state.target - (universalNodeConjunction state row address
      priorValues).state.next) (universalNodeConjunction state row address priorValues).state.next
      (selectiveSelectedCode (universalNodeConjunction state row address
      priorValues).state.selected) (rawCircuitNodeCode (n := descriptionWidth width bound)
      (BooleanNode.or (universalNodeLeft state row priorValues).output (universalNodeRight state
      row priorValues).output)))
  , natBitLength (Nat.pair 0 (selectiveWireCode (universalNodeDisjunction state row address
      priorValues)))
  , natBitLength (selectiveFieldSelectInput (selectiveStateCode (universalNodeDisjunction state
      row address priorValues).state) (descriptionWidth width bound) (row.val * rowWidth width
      bound) 0 6 (encodeTaggedList (universalNodeCases state row address priorValues)))
  , natBitLength (Nat.pair 0 (selectiveWireCode (selectiveCompileUniversalNode state row address
      priorValues)))
  , fieldRunner.bits (universalNodeDisjunction state row address priorValues).state row 0 6
      (universalNodeTagBlock width bound) (universalNodeCases state row address priorValues)
  ]

/-- Register width of one universal-evaluator row compilation. -/
def selectiveUniversalNodeRunBits {width bound : ℕ}
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (addressRunner : SelectiveAddressSelectRunner width bound)
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width)
    (priorValues : List ℕ) : ℕ :=
  (universalNodeBitsTerms fieldRunner addressRunner state row address
    priorValues).foldr max 0

/-- Interpreter fuel of one universal-evaluator row compilation. -/
def selectiveUniversalNodeRunFuel {width bound : ℕ}
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (addressRunner : SelectiveAddressSelectRunner width bound)
    (state : SelectiveState (descriptionWidth width bound))
    (row : Fin (bound + 1)) (address : BitInput width)
    (priorValues : List ℕ) : ℕ :=
  260 + (fieldRunner.fuel state row 6 (boundedCircuitFieldLimit width bound)
    (universalNodeFirstBlock width bound) priorValues + (fieldRunner.fuel (universalNodeLeft state
    row priorValues).state row (6 + (boundedCircuitFieldLimit width bound))
    (boundedCircuitFieldLimit width bound) (universalNodeSecondBlock width bound) priorValues +
    (selectiveUnaryRunFuel (universalNodeRight state row priorValues).state
    (selectiveUnaryEqualsLiterals (n := width) row 6 (boundedCircuitFieldLimit width bound) 1
    (universalNodeFirstBlock width bound)) + (addressRunner.fuel (universalNodeConstant state row
    priorValues).state row address + (selectiveEmitFuel ((universalNodeInputValue state row
    address priorValues).state.target - (universalNodeInputValue state row address
    priorValues).state.next) (selectiveSelectedCode (universalNodeInputValue state row address
    priorValues).state.selected) + (selectiveEmitFuel ((universalNodeNegated state row address
    priorValues).state.target - (universalNodeNegated state row address priorValues).state.next)
    (selectiveSelectedCode (universalNodeNegated state row address priorValues).state.selected) +
    (selectiveEmitFuel ((universalNodeConjunction state row address priorValues).state.target -
    (universalNodeConjunction state row address priorValues).state.next) (selectiveSelectedCode
    (universalNodeConjunction state row address priorValues).state.selected) + fieldRunner.fuel
    (universalNodeDisjunction state row address priorValues).state row 0 6 (universalNodeTagBlock
    width bound) (universalNodeCases state row address priorValues))))))))

set_option maxHeartbeats 1600000 in

/-- **The universal-evaluator row compiler's run, from the two levels below
it.**  The `641`-instruction stream compiles exactly the row the source
compiler produces.  Only the field selector and the address selector remain as
premises; the unary compiler and the append transition are consumed
opaquely. -/
def selectiveUniversalNodeRunnerOfLevels {width bound : ℕ}
    (fieldRunner : SelectiveFieldSelectRunner width bound)
    (addressRunner : SelectiveAddressSelectRunner width bound) :
    SelectiveUniversalNodeRunner width bound where
  bits := selectiveUniversalNodeRunBits fieldRunner addressRunner
  fuel := selectiveUniversalNodeRunFuel fieldRunner addressRunner
  executes := by
    intro state row address priorValues hordered entry hentryPc hentryInput
    have hbits :
        selectiveUniversalNodeRunBits fieldRunner addressRunner state row
            address priorValues ≤
          selectiveUniversalNodeRunBits fieldRunner addressRunner state row
            address priorValues := le_refl _
    unfold selectiveUniversalNodeRunBits universalNodeBitsTerms at hbits
    simp only [List.foldr_cons, List.foldr_nil] at hbits
    have hsevenBits := (Nat.le_max_left _ _).trans hbits
    have htail0 := (Nat.le_max_right _ _).trans hbits
    have hrequestBits := (Nat.le_max_left _ _).trans htail0
    have htail1 := (Nat.le_max_right _ _).trans htail0
    have hleftRequestBits := (Nat.le_max_left _ _).trans htail1
    have htail2 := (Nat.le_max_right _ _).trans htail1
    have hleftWireBits := (Nat.le_max_left _ _).trans htail2
    have htail3 := (Nat.le_max_right _ _).trans htail2
    have hleftCalleeBits := (Nat.le_max_left _ _).trans htail3
    have htail4 := (Nat.le_max_right _ _).trans htail3
    have hrightRequestBits := (Nat.le_max_left _ _).trans htail4
    have htail5 := (Nat.le_max_right _ _).trans htail4
    have hrightWireBits := (Nat.le_max_left _ _).trans htail5
    have htail6 := (Nat.le_max_right _ _).trans htail5
    have hrightCalleeBits := (Nat.le_max_left _ _).trans htail6
    have htail7 := (Nat.le_max_right _ _).trans htail6
    have hconstantRequestBits := (Nat.le_max_left _ _).trans htail7
    have htail8 := (Nat.le_max_right _ _).trans htail7
    have hconstantWireBits := (Nat.le_max_left _ _).trans htail8
    have htail9 := (Nat.le_max_right _ _).trans htail8
    have hconstantCalleeBits := (Nat.le_max_left _ _).trans htail9
    have htail10 := (Nat.le_max_right _ _).trans htail9
    have haddressRequestBits := (Nat.le_max_left _ _).trans htail10
    have htail11 := (Nat.le_max_right _ _).trans htail10
    have haddressWireBits := (Nat.le_max_left _ _).trans htail11
    have htail12 := (Nat.le_max_right _ _).trans htail11
    have haddressCalleeBits := (Nat.le_max_left _ _).trans htail12
    have htail13 := (Nat.le_max_right _ _).trans htail12
    have hnotInputBits := (Nat.le_max_left _ _).trans htail13
    have htail14 := (Nat.le_max_right _ _).trans htail13
    have hnotWireBits := (Nat.le_max_left _ _).trans htail14
    have htail15 := (Nat.le_max_right _ _).trans htail14
    have handInputBits := (Nat.le_max_left _ _).trans htail15
    have htail16 := (Nat.le_max_right _ _).trans htail15
    have handWireBits := (Nat.le_max_left _ _).trans htail16
    have htail17 := (Nat.le_max_right _ _).trans htail16
    have horInputBits := (Nat.le_max_left _ _).trans htail17
    have htail18 := (Nat.le_max_right _ _).trans htail17
    have horWireBits := (Nat.le_max_left _ _).trans htail18
    have htail19 := (Nat.le_max_right _ _).trans htail18
    have htagRequestBits := (Nat.le_max_left _ _).trans htail19
    have htail20 := (Nat.le_max_right _ _).trans htail19
    have htagWireBits := (Nat.le_max_left _ _).trans htail20
    have htail21 := (Nat.le_max_right _ _).trans htail20
    have htagCalleeBits := (Nat.le_max_left _ _).trans htail21
    unfold selectiveUniversalNodeRunFuel
    refine run_selectiveUniversalNodeProgram_of_wires state (universalNodeLeft state row
      priorValues) (universalNodeRight state row priorValues) (universalNodeConstant state row
      priorValues)
      (universalNodeInputValue state row address priorValues) (universalNodeNegated state row
        address priorValues) (universalNodeConjunction state row address priorValues)
        (universalNodeDisjunction state row address priorValues) (selectiveCompileUniversalNode
        state row address priorValues) (row.val * rowWidth width bound) (boundedCircuitFieldLimit
        width bound) width
      (encodeBitInput address) (encodeTaggedList priorValues)
      (encodeTaggedList (universalNodeCases state row address priorValues)) _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _
      rfl rfl rfl rfl rfl rfl rfl
      (universalNodeNegated_eq state row address priorValues)
      (universalNodeConjunction_eq state row address priorValues)
      (universalNodeDisjunction_eq state row address priorValues)
      (universalNodeCasesCode_eq state row address priorValues)
      (universalNodeInputValue_ordered state row address priorValues hordered)
      (universalNodeNegated_ordered state row address priorValues hordered)
      (universalNodeConjunction_ordered state row address priorValues hordered)
      rfl rfl rfl ?_ ?_ ?_ ?_ ?_ hsevenBits hrequestBits hleftRequestBits
      hleftWireBits hrightRequestBits hrightWireBits hconstantRequestBits
      hconstantWireBits haddressRequestBits haddressWireBits hnotInputBits
      hnotWireBits handInputBits handWireBits horInputBits horWireBits
      htagRequestBits htagWireBits entry hentryPc hentryInput
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (fieldRunner.executes state row 6 (boundedCircuitFieldLimit width bound) priorValues
          (universalNodeFirstBlock width bound) hordered
          frame hframePc hframeInput) hleftCalleeBits
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (fieldRunner.executes (universalNodeLeft state row priorValues).state row (6 +
          (boundedCircuitFieldLimit width bound)) (boundedCircuitFieldLimit width bound)
          priorValues
          (universalNodeSecondBlock width bound)
          (universalNodeLeft_ordered state row priorValues hordered) frame
          hframePc hframeInput) hrightCalleeBits
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (run_selectiveUnaryProgram_eq_unaryEquals (universalNodeRight state row priorValues).state
          row 6 (boundedCircuitFieldLimit width bound) 1
          (universalNodeFirstBlock width bound)
          (universalNodeRight_ordered state row priorValues hordered) frame
          hframePc hframeInput) hconstantCalleeBits
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (addressRunner.executes (universalNodeConstant state row priorValues).state row address
          (universalNodeConstant_ordered state row priorValues hordered) frame
          hframePc hframeInput) haddressCalleeBits
    · intro frame hframePc hframeInput
      exact run_bits_mono
        (fieldRunner.executes (universalNodeDisjunction state row address priorValues).state row 0
          6 (universalNodeCases state row address priorValues) (universalNodeTagBlock width bound)
          (universalNodeDisjunction_ordered state row address priorValues
            hordered) frame hframePc hframeInput) htagCalleeBits

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
