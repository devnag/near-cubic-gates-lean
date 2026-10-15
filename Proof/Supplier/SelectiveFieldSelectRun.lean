import Proof.Supplier.SelectiveUnaryRun
import Batteries.Tactic.OpenPrivate

/-!
# The field selector's run

`selectiveFieldSelectProgram` is the `196`-instruction stream that compiles one
guarded selection over a description row: a controller of `81` instructions with
two relocated callees, the `97`-instruction unary-equality compiler and the
`18`-instruction append transition.

The controller compiles `selectiveCompileGuardedAny` over the choices
`values.zipIdx.map fun entry => (fieldEquals row entry.2, entry.1)`.  Its
forward pass runs the unary callee once per values entry, appends the guarded
conjunction of that condition against the entry's own wire, and retains the
conjunction's output on a private reverse spine; its reverse pass then rebuilds
the source compiler's right-associated disjunction from the explicit `false`
base case, one append per spine entry.  Both passes are proved here, so the
unary compiler's own (already closed) run is the only level fact this module
consumes.
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
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

open private selectiveFieldSelectInput selectiveFieldSelectControllerProgram
  selectiveFieldSelectControllerProgram_length selectiveFieldSelectProgram
  selectiveFieldSelectProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

open private selectiveCompileGuardedAny_ordered from
  Proof.Supplier.SelectiveCountCasesRun

/-! ## 1. The controller's two passes, at the typed level

The source compiler folds a guarded disjunction to the right, so the outermost
`or` node is appended last and its left child is the first choice's guarded
conjunction.  The controller instead compiles every choice first, retains their
guarded outputs on a reverse spine, and only then emits the disjunctions from
the innermost outwards.  Both orders append exactly the same nodes in exactly
the same order; §1 proves that.
-/

/-- The forward pass: one guarded conjunction per choice, in the ascending
order the controller visits them. -/
def selectiveFieldSelectHeads {n : ℕ} :
    SelectiveState n → List (BoolExpr n × ℕ) → SelectiveWireList n
  | state, [] => { state := state, values := [] }
  | state, choice :: rest =>
      let condition := selectiveCompileExpr state choice.1
      let guarded := selectiveAnd condition.state condition.output choice.2
      let tail := selectiveFieldSelectHeads guarded.state rest
      { state := tail.state
        values := guarded.output :: tail.values }

theorem selectiveFieldSelectHeads_ordered {n : ℕ}
    (choices : List (BoolExpr n × ℕ)) (state : SelectiveState n)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered (selectiveFieldSelectHeads state choices).state := by
  induction choices generalizing state with
  | nil => exact hordered
  | cons choice rest ih =>
      exact ih _
        (selectiveState_emit_ordered _ _
          (selectiveCompileExpr_ordered state choice.1 hordered))

/-- **The controller's scheduling identity.**  The source compiler's
right-associated guarded disjunction is exactly the forward choice pass
followed by the reverse fold over the retained spine. -/
theorem selectiveCompileGuardedAny_eq_fold {n : ℕ}
    (choices : List (BoolExpr n × ℕ)) (state : SelectiveState n) :
    selectiveCompileGuardedAny state choices =
      selectiveCountCasesFold
        (selectiveConst (selectiveFieldSelectHeads state choices).state
          false).state
        (selectiveConst (selectiveFieldSelectHeads state choices).state
          false).output
        (selectiveFieldSelectHeads state choices).values.reverse := by
  induction choices generalizing state with
  | nil =>
      rw [selectiveCompileGuardedAny]
      rfl
  | cons choice rest ih =>
      rw [selectiveCompileGuardedAny]
      simp only [selectiveFieldSelectHeads, List.reverse_cons]
      rw [selectiveCountCasesFold_concat]
      rw [ih]

/-- The choice list the controller walks from one starting values index: one
unary equality test per entry, against consecutive indices. -/
def selectiveFieldSelectChoices {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    ℕ → List ℕ → List (BoolExpr (descriptionWidth n bound) × ℕ)
  | _, [] => []
  | index, value :: rest =>
      (unaryEqualsExpr row start limit index hblock, value) ::
        selectiveFieldSelectChoices row start limit hblock (index + 1) rest

@[simp] theorem selectiveFieldSelectChoices_nil {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit index : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    selectiveFieldSelectChoices (n := n) row start limit hblock index [] =
      [] := rfl

theorem selectiveFieldSelectChoices_eq_zipIdx {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (index : ℕ) (values : List ℕ) :
    selectiveFieldSelectChoices (n := n) row start limit hblock index values =
      (values.zipIdx index).map fun entry =>
        (unaryEqualsExpr row start limit entry.2 hblock, entry.1) := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
      rw [selectiveFieldSelectChoices, List.zipIdx_cons, List.map_cons, ih]

/-- The condition wire of one choice: the relocated unary compiler's compiled
equality test at that choice's values index. -/
def selectiveFieldSelectCondition {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr state
    (unaryEqualsExpr (n := n) row start limit index hblock)

/-- The guarded conjunction of one choice: its condition against its own
retained value. -/
def selectiveFieldSelectGuarded {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound))
    (index value : ℕ) : SelectiveWire (descriptionWidth n bound) :=
  selectiveAnd
    (selectiveFieldSelectCondition row start limit hblock state index).state
    (selectiveFieldSelectCondition row start limit hblock state index).output
    value

theorem selectiveFieldSelectCondition_ordered {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveFieldSelectCondition row start limit hblock state
        index).state :=
  selectiveCompileExpr_ordered state _ hordered

theorem selectiveFieldSelectGuarded_ordered {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound))
    (index value : ℕ) (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveFieldSelectGuarded row start limit hblock state index
        value).state :=
  selectiveState_emit_ordered _ _
    (selectiveFieldSelectCondition_ordered row start limit hblock state index
      hordered)

/-! ## 2. Decoding the fixed 196-instruction stream

The controller occupies the first `81` positions, the unary callee the next
`97`, and the append callee the last `18`.  Every later step decodes through
exactly one of the three lemmas below, so no proof ever forces the whole
instruction list. -/

private theorem selectiveFieldSelectProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveFieldSelectControllerProgram 81 178)[pc]? = some instruction) :
    selectiveFieldSelectProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveFieldSelectControllerProgram 81 178).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveFieldSelectControllerProgram_length] at hpc
  simp only [selectiveFieldSelectProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFieldSelectControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveFieldSelectControllerProgram_length]
    omega)]
  exact hlookup

theorem selectiveFieldSelectProgram_unaryCallable :
    ProgramCallableAt selectiveFieldSelectProgram selectiveUnaryProgram
      81 1000 50 68 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUnaryProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUnaryProgram_length] at hpc
  simp only [selectiveFieldSelectProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFieldSelectControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveFieldSelectControllerProgram_length]
    omega)]
  simp only [selectiveFieldSelectControllerProgram_length]
  rw [show 81 + pc - 81 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveFieldSelectProgram_emitCallable :
    ProgramCallableAt selectiveFieldSelectProgram selectiveEmitProgram
      178 2000 50 68 := by
  intro pc instruction hlookup
  simp only [selectiveFieldSelectProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveFieldSelectControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveFieldSelectControllerProgram_length,
    selectiveUnaryProgram_length]
  rw [show 178 + pc - (81 + 97) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The two shared call frames

All four append sites of this controller — the guarded conjunction, the `false`
base case and every disjunction — reach the relocated append through the same
physical block at `63`; both unary-equality sites reach the relocated unary
compiler through the same physical block at `54`.  Each block builds the
callee's request from the live state registers, runs the callee, and unpacks
the returned wire back into those same registers; both then fall through to the
shared phase dispatcher at `75`.  Every later trace in this module goes through
one of these two lemmas. -/

-- Five request-building steps around the relocated append, then seven steps
-- unpacking the returned wire back into the controller's live registers.
private theorem run_selectiveFieldSelectEmitCall {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity rowBase start limit values index spine head accumulated
      phase : ℕ)
    (machine : NPOracleState)
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
    (hpc : machine.pc = 63)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 21 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hrowBase : machine.registers 10 = rowBase)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hvalues : machine.registers 15 = values)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = spine)
    (hhead : machine.registers 18 = head)
    (haccumulated : machine.registers 28 = accumulated)
    (hphase : machine.registers 30 = phase)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 75 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 25 = (state.emit node).output →
      resumed.registers 8 = arity →
      resumed.registers 10 = rowBase →
      resumed.registers 12 = start →
      resumed.registers 14 = limit →
      resumed.registers 15 = values →
      resumed.registers 16 = index →
      resumed.registers 17 = spine →
      resumed.registers 18 = head →
      resumed.registers 28 = accumulated →
      resumed.registers 30 = phase →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFieldSelectProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState n,
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hinputForm :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected) (rawCircuitNodeCode node) =
        Nat.pair (selectiveStateCode state) (rawCircuitNodeCode node) := rfl
  have hinputFlat := hinputBits
  rw [hinputForm] at hinputFlat
  have hstateBits := natBitLength_pair_left hinputFlat
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  simp only [selectiveWireCode] at hwireParts
  have hemittedStateBits := natBitLength_pair_left hwireParts
  have hemittedOutputBits := natBitLength_pair_right hwireParts
  have hemittedStateFlat := hemittedStateBits
  rw [hstateForm (state.emit node).state] at hemittedStateFlat
  have hemittedRemainingBits := natBitLength_pair_left hemittedStateFlat
  have hemittedTailBits := natBitLength_pair_right hemittedStateFlat
  have hemittedNextBits := natBitLength_pair_left hemittedTailBits
  have hemittedSelectedBits := natBitLength_pair_right hemittedTailBits
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
    (4 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveFieldSelectProgram_controllerAt (pc := 63) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveFieldSelectProgram_controllerAt (pc := 64) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 3 + (emitFuel + (7 + extraFuel)) =
    (2 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveFieldSelectProgram_controllerAt (pc := 65) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 66) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 67) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveFieldSelectProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state node hordered frame hframePc ?_)
      hemitCalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro emitHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (state.emit node))
      (selectiveFieldSelectProgram_controllerAt (pc := 68) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveFieldSelectProgram_controllerAt (pc := 69) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveFieldSelectProgram_controllerAt (pc := 70) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (state.emit node).state.target - (state.emit node).state.next)
      (selectiveFieldSelectProgram_controllerAt (pc := 71) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveFieldSelectProgram_controllerAt (pc := 72) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveFieldSelectProgram_controllerAt (pc := 73) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveFieldSelectProgram_controllerAt (pc := 74) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hstart, hlimit, hvalues, hindex, hspine, hhead,
        haccumulated, hphase]

-- Nine request-building steps around the relocated unary compiler, then the
-- same seven unpacking steps.
private theorem run_selectiveFieldSelectUnaryCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit index : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (maximumBits unaryFuel extraFuel finalOutput : ℕ)
    (values spine head accumulated phase : ℕ)
    (machine : NPOracleState)
    (hunaryFuel :
      unaryFuel =
        selectiveUnaryRunFuel state
          (selectiveUnaryEqualsLiterals (n := n) row start limit index hblock))
    (hcalleeBits :
      selectiveUnaryRunBits state
          (selectiveUnaryEqualsLiterals (n := n) row start limit index hblock)
          (row.val * rowWidth n bound) start index ≤
        maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUnaryInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound) start
            limit index) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveFieldSelectCondition row start limit hblock state
                index))) ≤
        maximumBits)
    (hpc : machine.pc = 54)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth n bound)
    (hrowBase : machine.registers 10 = row.val * rowWidth n bound)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hvalues : machine.registers 15 = values)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = spine)
    (hhead : machine.registers 18 = head)
    (haccumulated : machine.registers 28 = accumulated)
    (hphase : machine.registers 30 = phase)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 75 →
      resumed.registers 4 =
        (selectiveFieldSelectCondition row start limit hblock state
            index).state.target -
          (selectiveFieldSelectCondition row start limit hblock state
            index).state.next →
      resumed.registers 6 =
        (selectiveFieldSelectCondition row start limit hblock state index).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveFieldSelectCondition row start limit hblock state
            index).state.selected →
      resumed.registers 25 =
        (selectiveFieldSelectCondition row start limit hblock state index).output →
      resumed.registers 8 = descriptionWidth n bound →
      resumed.registers 10 = row.val * rowWidth n bound →
      resumed.registers 12 = start →
      resumed.registers 14 = limit →
      resumed.registers 15 = values →
      resumed.registers 16 = index →
      resumed.registers 17 = spine →
      resumed.registers 18 = head →
      resumed.registers 28 = accumulated →
      resumed.registers 30 = phase →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFieldSelectProgram maximumBits
        (9 + (unaryFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
          (row.val * rowWidth n bound) start limit index =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (descriptionWidth n bound)
            (Nat.pair (row.val * rowWidth n bound)
              (Nat.pair start (Nat.pair limit index)))) := rfl
  have hrequestFlat := hrequestBits
  rw [hrequestForm] at hrequestFlat
  have hstateBits := natBitLength_pair_left hrequestFlat
  have htailOne := natBitLength_pair_right hrequestFlat
  have htailTwo := natBitLength_pair_right htailOne
  have htailThree := natBitLength_pair_right htailTwo
  have htailFour := natBitLength_pair_right htailThree
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  have hwireFlat := natBitLength_pair_right hwireBits
  have hwireParts := hwireFlat
  simp only [selectiveWireCode] at hwireParts
  have hcompiledStateBits := natBitLength_pair_left hwireParts
  have hcompiledOutputBits := natBitLength_pair_right hwireParts
  have hcompiledStateFlat := hcompiledStateBits
  rw [hstateForm] at hcompiledStateFlat
  have hcompiledRemainingBits := natBitLength_pair_left hcompiledStateFlat
  have hcompiledTailBits := natBitLength_pair_right hcompiledStateFlat
  have hcompiledNextBits := natBitLength_pair_left hcompiledTailBits
  have hcompiledSelectedBits := natBitLength_pair_right hcompiledTailBits
  rw [show 9 + (unaryFuel + (7 + extraFuel)) =
    (8 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveFieldSelectProgram_controllerAt (pc := 54) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 8 + (unaryFuel + (7 + extraFuel)) =
    (7 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveFieldSelectProgram_controllerAt (pc := 55) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 7 + (unaryFuel + (7 + extraFuel)) =
    (6 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair limit index)
    (selectiveFieldSelectProgram_controllerAt (pc := 56) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit, hindex])
    htailFour]
  rw [show 6 + (unaryFuel + (7 + extraFuel)) =
    (5 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair start (Nat.pair limit index))
    (selectiveFieldSelectProgram_controllerAt (pc := 57) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) htailThree]
  rw [show 5 + (unaryFuel + (7 + extraFuel)) =
    (4 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair start (Nat.pair limit index)))
    (selectiveFieldSelectProgram_controllerAt (pc := 58) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htailTwo]
  rw [show 4 + (unaryFuel + (7 + extraFuel)) =
    (3 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair start (Nat.pair limit index))))
    (selectiveFieldSelectProgram_controllerAt (pc := 59) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) htailOne]
  rw [show 3 + (unaryFuel + (7 + extraFuel)) =
    (2 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
        (row.val * rowWidth n bound) start limit index)
    (selectiveFieldSelectProgram_controllerAt (pc := 60) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [show 2 + (unaryFuel + (7 + extraFuel)) =
    (1 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 61) rfl) rfl hzeroBits]
  rw [show 1 + (unaryFuel + (7 + extraFuel)) =
    (unaryFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 62) rfl) rfl]
  simp only [ite_self]
  rw [hunaryFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveUnaryProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveFieldSelectCondition row start limit hblock state index))
    selectiveFieldSelectProgram_unaryCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveUnaryProgram_eq_unaryEquals state row start limit index
        hblock hordered frame hframePc ?_)
      hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro unaryHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveFieldSelectCondition row start limit hblock state index))
      (selectiveFieldSelectProgram_controllerAt (pc := 68) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveFieldSelectCondition row start limit hblock state index).state)
      (selectiveFieldSelectProgram_controllerAt (pc := 69) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveFieldSelectCondition row start limit hblock state index).output)
      (selectiveFieldSelectProgram_controllerAt (pc := 70) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveFieldSelectCondition row start limit hblock state
            index).state.target -
          (selectiveFieldSelectCondition row start limit hblock state
            index).state.next)
      (selectiveFieldSelectProgram_controllerAt (pc := 71) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm
            (selectiveFieldSelectCondition row start limit hblock state
              index).state])
      hcompiledRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveFieldSelectCondition row start limit hblock state index).state.next
          (selectiveSelectedCode
            (selectiveFieldSelectCondition row start limit hblock state
              index).state.selected))
      (selectiveFieldSelectProgram_controllerAt (pc := 72) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm
            (selectiveFieldSelectCondition row start limit hblock state
              index).state])
      hcompiledTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveFieldSelectCondition row start limit hblock state index).state.next)
      (selectiveFieldSelectProgram_controllerAt (pc := 73) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveFieldSelectCondition row start limit hblock state
            index).state.selected)
      (selectiveFieldSelectProgram_controllerAt (pc := 74) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hstart, hlimit, hvalues, hindex, hspine, hhead,
        haccumulated, hphase]

/-! ## 4. The reverse disjunction fold

Interpreter resources on this level are data dependent, so the fold's clock is
defined by the same recursion as its output.  The retained values and the
private reverse spine share the one tagged-cons encoding already fixed by the
outermost controller. -/

/-- Interpreter fuel of the reverse fold: eleven controller steps, one
relocated append, and an eight-step phase dispatch per retained choice. -/
def selectiveFieldSelectFoldFuel {n : ℕ} :
    SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      11 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              (8 +
                selectiveFieldSelectFoldFuel
                  (selectiveOr state value accumulated).state
                  (selectiveOr state value accumulated).output rest))))

-- One fold iteration is eleven controller steps and an eight-step phase
-- dispatch around the shared append frame of §3.
private theorem run_selectiveFieldSelectFoldStep {n : ℕ}
    (state : SelectiveState n) (accumulated value : ℕ) (rest : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hspineBits :
      natBitLength (selectiveCountCasesSpineCode (value :: rest)) ≤
        maximumBits)
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.or value accumulated))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode (selectiveOr state value accumulated))) ≤
        maximumBits)
    (hpc : machine.pc = 40)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hspine :
      machine.registers 17 = selectiveCountCasesSpineCode (value :: rest))
    (haccumulated : machine.registers 28 = accumulated)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 40 →
      resumed.registers 0 =
        selectiveWireCode (selectiveOr state value accumulated) →
      resumed.registers 4 =
        (selectiveOr state value accumulated).state.target -
          (selectiveOr state value accumulated).state.next →
      resumed.registers 6 = (selectiveOr state value accumulated).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveOr state value accumulated).state.selected →
      resumed.registers 8 = n →
      resumed.registers 17 = selectiveCountCasesSpineCode rest →
      resumed.registers 28 = (selectiveOr state value accumulated).output →
      runNPOracleProgram selectiveFieldSelectProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFieldSelectProgram maximumBits
        (11 + (5 + (emitFuel + (7 + (8 + extraFuel))))) machine =
      some finalOutput := by
  have hnodeCode :
      rawCircuitNodeCode (n := n) (.or value accumulated) =
        Nat.pair 4 (Nat.pair (n + value) (n + accumulated)) := rfl
  have hemitInput :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.or value accumulated)) =
        Nat.pair (selectiveStateCode state)
          (rawCircuitNodeCode (n := n) (.or value accumulated)) := rfl
  have hwireForm :
      selectiveWireCode (selectiveOr state value accumulated) =
        Nat.pair
          (selectiveStateCode (selectiveOr state value accumulated).state)
          (selectiveOr state value accumulated).output := rfl
  have hspineForm :
      selectiveCountCasesSpineCode (value :: rest) =
        Nat.pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest)) := rfl
  have hconsBits :
      natBitLength (Nat.pair value (selectiveCountCasesSpineCode rest)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  have hvalueBits : natBitLength value ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair value _)).trans hconsBits
  have htailSpineBits :
      natBitLength (selectiveCountCasesSpineCode rest) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair value _)).trans hconsBits
  have hcodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.or value accumulated)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hinputBits
    rw [hemitInput]
    exact Nat.right_le_pair _ _
  have hchildrenBits :
      natBitLength (Nat.pair (n + value) (n + accumulated)) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.right_le_pair 4 _
  have hleftChildBits : natBitLength (n + value) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
  have hrightChildBits : natBitLength (n + accumulated) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
  have hfourBits : natBitLength 4 ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.left_le_pair 4 _
  have hthreeBits : natBitLength 3 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  have htwoBits : natBitLength 2 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hfourBits
  have houtputWireBits :
      natBitLength (selectiveWireCode (selectiveOr state value accumulated)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 0 _)).trans hwireBits
  have hnextOutputBits :
      natBitLength (selectiveOr state value accumulated).output ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans houtputWireBits
    rw [hwireForm]
    exact Nat.right_le_pair _ _
  have hspineNonzero : machine.registers 17 ≠ 0 := by
    rw [hspine, hspineForm]
    have hone :=
      Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
    omega
  rw [show 11 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (10 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 40) rfl) hpc]
  rw [if_neg hspineNonzero]
  rw [show 10 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (9 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair value (selectiveCountCasesSpineCode rest))
    (selectiveFieldSelectProgram_controllerAt (pc := 41) rfl) rfl
    (by simp [NPOracleState.jump, hspine, hspineForm]) hconsBits]
  rw [show 9 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (8 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_unpairLeft_instruction (value := value)
    (selectiveFieldSelectProgram_controllerAt (pc := 42) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 8 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (7 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveCountCasesSpineCode rest)
    (selectiveFieldSelectProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
  rw [show 7 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (6 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_add_instruction (value := n + value)
    (selectiveFieldSelectProgram_controllerAt (pc := 44) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hleftChildBits]
  rw [show 6 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (5 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_add_instruction (value := n + accumulated)
    (selectiveFieldSelectProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, haccumulated])
    hrightChildBits]
  rw [show 5 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (4 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + value) (n + accumulated))
    (selectiveFieldSelectProgram_controllerAt (pc := 46) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 4 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (3 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 47) rfl) rfl hfourBits]
  rw [show 3 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (2 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.or value accumulated))
    (selectiveFieldSelectProgram_controllerAt (pc := 48) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 2 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (1 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 49) rfl) rfl hthreeBits]
  rw [show 1 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (5 + (emitFuel + (7 + (8 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 50) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveFieldSelectEmitCall state (.or value accumulated) hordered
    maximumBits emitFuel (8 + extraFuel) finalOutput n (machine.registers 10)
    (machine.registers 12) (machine.registers 14) (machine.registers 15)
    (machine.registers 16) (selectiveCountCasesSpineCode rest) value
    accumulated 3 _ hemitFuel hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, haccumulated]
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
      hresumedSelected hresumedOutput hresumedArity _ _ _ _ _ hresumedSpine _ _
      hresumedPhase
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveFieldSelectProgram_controllerAt (pc := 75) rfl) hresumedPc]
    rw [if_neg (by simp [hresumedPhase])]
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := 2)
      (selectiveFieldSelectProgram_controllerAt (pc := 76) rfl) rfl
      (by simp [NPOracleState.jump, hresumedPhase]) htwoBits]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveFieldSelectProgram_controllerAt (pc := 77) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := 1)
      (selectiveFieldSelectProgram_controllerAt (pc := 78) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) honeBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveFieldSelectProgram_controllerAt (pc := 79) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveFieldSelectProgram_controllerAt (pc := 80) rfl) rfl]
    simp only [ite_self]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_copy_instruction
      (value := (selectiveOr state value accumulated).output)
      (selectiveFieldSelectProgram_controllerAt (pc := 51) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, selectiveOr,
          hresumedOutput])
      hnextOutputBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveFieldSelectProgram_controllerAt (pc := 52) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveOr] using
        hresumedWire
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveOr] using
        hresumedRemaining
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveOr] using
        hresumedNext
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveOr] using
        hresumedSelected
    · simpa [NPOracleState.write, NPOracleState.jump] using hresumedArity
    · simpa [NPOracleState.write, NPOracleState.jump] using hresumedSpine
    · simp [NPOracleState.write, NPOracleState.jump]

-- The fold is one induction on the retained spine.
private theorem run_selectiveFieldSelectFoldLoop {n : ℕ}
    (values : List ℕ) (state : SelectiveState n) (accumulated : ℕ)
    (hordered : selectiveStateOrdered state) (maximumBits : ℕ)
    (hbits :
      natBitLength
          (selectiveCountCasesFoldWorkBound state accumulated values) ≤
        maximumBits)
    (machine : NPOracleState) (hpc : machine.pc = 40)
    (hwire :
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hspine : machine.registers 17 = selectiveCountCasesSpineCode values)
    (haccumulated : machine.registers 28 = accumulated) :
    runNPOracleProgram selectiveFieldSelectProgram maximumBits
        (selectiveFieldSelectFoldFuel state accumulated values) machine =
      some
        (selectiveWireCode
          (selectiveCountCasesFold state accumulated values)) := by
  induction values generalizing state accumulated machine with
  | nil =>
      have hfuel :
          selectiveFieldSelectFoldFuel state accumulated ([] : List ℕ) =
            (0 + 1) + 1 := rfl
      have hfoldNil :
          selectiveWireCode
              (selectiveCountCasesFold state accumulated ([] : List ℕ)) =
            Nat.pair (selectiveStateCode state) accumulated := rfl
      rw [hfuel]
      rw [run_branchZero_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 40) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      refine run_halt_instruction (fuel := 0)
        (selectiveFieldSelectProgram_controllerAt (pc := 53) rfl) rfl ?_ ?_
      · rw [hfoldNil]
        exact hwire
      · rw [hfoldNil]
        exact hbits
  | cons value rest ih =>
      have hfuel :
          selectiveFieldSelectFoldFuel state accumulated (value :: rest) =
            11 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    (8 +
                      selectiveFieldSelectFoldFuel
                        (selectiveOr state value accumulated).state
                        (selectiveOr state value accumulated).output
                        rest)))) := rfl
      have hworkCons :
          selectiveCountCasesFoldWorkBound state accumulated (value :: rest) =
            max (selectiveCountCasesSpineCode (value :: rest))
              (max
                (selectiveEmitInput (state.target - state.next) state.next
                  (selectiveSelectedCode state.selected)
                  (rawCircuitNodeCode (n := n) (.or value accumulated)))
                (max
                  (Nat.pair 0
                    (selectiveWireCode (selectiveOr state value accumulated)))
                  (selectiveCountCasesFoldWorkBound
                    (selectiveOr state value accumulated).state
                    (selectiveOr state value accumulated).output rest))) := rfl
      rw [hworkCons] at hbits
      have hspineBits := (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
      have hbitsTail := (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
      have hinputBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTail
      have hbitsTailTwo :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTail
      have hwireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTailTwo
      have hrecBits :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTailTwo
      rw [hfuel]
      refine run_selectiveFieldSelectFoldStep state accumulated value rest
        hordered maximumBits _ _ _ machine rfl hspineBits hinputBits hwireBits
        hpc hremaining hnext hselected harity hspine haccumulated ?_
      intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedSpine hresumedAccumulated
      exact ih _ _
        (selectiveState_emit_ordered state (.or value accumulated) hordered)
        hrecBits _ hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedSpine hresumedAccumulated

/-! ## 5. The forward choice pass

Each values entry is compiled by one call to the relocated unary compiler at
that entry's own index, guarded against the entry's own retained wire, and
retained on the private reverse spine.  The choice list the controller walks is
fixed by the starting values index and the values list alone. -/

/-- The wire the controller is committed to once it reaches the choice loop
head with the given retained spine. -/
def selectiveFieldSelectForwardOutput {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (values spine : List ℕ) : SelectiveWire (descriptionWidth n bound) :=
  selectiveCountCasesFold
    (selectiveConst
      (selectiveFieldSelectHeads state
        (selectiveFieldSelectChoices row start limit hblock index
          values)).state false).state
    (selectiveConst
      (selectiveFieldSelectHeads state
        (selectiveFieldSelectChoices row start limit hblock index
          values)).state false).output
    ((selectiveFieldSelectHeads state
      (selectiveFieldSelectChoices row start limit hblock index
        values)).values.reverse ++ spine)

private theorem selectiveFieldSelectForwardOutput_nil {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (spine : List ℕ) :
    selectiveFieldSelectForwardOutput row start limit hblock state index []
        spine =
      selectiveCountCasesFold (selectiveConst state false).state
        (selectiveConst state false).output spine := rfl

private theorem selectiveFieldSelectForwardOutput_cons {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index value : ℕ)
    (rest spine : List ℕ) :
    selectiveFieldSelectForwardOutput row start limit hblock state index
        (value :: rest) spine =
      selectiveFieldSelectForwardOutput row start limit hblock
        (selectiveFieldSelectGuarded row start limit hblock state index
          value).state (index + 1) rest
        ((selectiveFieldSelectGuarded row start limit hblock state index
          value).output :: spine) := by
  simp only [selectiveFieldSelectForwardOutput, selectiveFieldSelectChoices,
    selectiveFieldSelectHeads, selectiveFieldSelectGuarded,
    selectiveFieldSelectCondition, List.reverse_cons, List.append_assoc,
    List.singleton_append]

/-- Interpreter fuel of the whole controller from the choice loop head. -/
def selectiveFieldSelectForwardFuel {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    SelectiveState (descriptionWidth n bound) → ℕ → List ℕ → List ℕ → ℕ
  | state, _, [], spine =>
      1 +
        (5 +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                (6 +
                  selectiveFieldSelectFoldFuel (selectiveConst state false).state
                    (selectiveConst state false).output spine)))))
  | state, index, value :: rest, spine =>
      6 +
        (9 +
          (selectiveUnaryRunFuel state
              (selectiveUnaryEqualsLiterals (n := n) row start limit index
                hblock) +
            (7 +
              (1 +
                (7 +
                  (5 +
                    (selectiveEmitFuel
                        ((selectiveFieldSelectCondition row start limit hblock
                          state index).state.target -
                          (selectiveFieldSelectCondition row start limit hblock
                            state index).state.next)
                        (selectiveSelectedCode
                          (selectiveFieldSelectCondition row start limit hblock
                            state index).state.selected) +
                      (7 +
                        (3 +
                          (5 +
                            selectiveFieldSelectForwardFuel row start limit
                              hblock
                              (selectiveFieldSelectGuarded row start limit
                                hblock state index value).state (index + 1) rest
                              ((selectiveFieldSelectGuarded row start limit
                                hblock state index value).output ::
                                spine)))))))))))

/-- Register-width envelope of the whole controller from the choice loop
head.  The `2` is the phase constant, which no request-derived value need
dominate. -/
def selectiveFieldSelectForwardBits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    SelectiveState (descriptionWidth n bound) → ℕ → List ℕ → List ℕ → ℕ
  | state, _, [], spine =>
      max (natBitLength 2) <|
        max
          (natBitLength
            (selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.const false)))) <|
          max
            (natBitLength
              (Nat.pair 0 (selectiveWireCode (selectiveConst state false)))) <|
            natBitLength
              (selectiveCountCasesFoldWorkBound (selectiveConst state false).state
                (selectiveConst state false).output spine)
  | state, index, value :: rest, spine =>
      max
        (selectiveUnaryRunBits state
          (selectiveUnaryEqualsLiterals (n := n) row start limit index hblock)
          (row.val * rowWidth n bound) start index) <|
        max
          (natBitLength
            (selectiveUnaryInput (selectiveStateCode state)
              (descriptionWidth n bound) (row.val * rowWidth n bound) start
              limit index)) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveFieldSelectCondition row start limit hblock state
                    index)))) <|
            max
              (natBitLength (selectiveCountCasesSpineCode (value :: rest))) <|
              max (natBitLength (index + 1)) <|
                max
                  (natBitLength
                    (selectiveEmitInput
                      ((selectiveFieldSelectCondition row start limit hblock
                        state index).state.target -
                        (selectiveFieldSelectCondition row start limit hblock
                          state index).state.next)
                      (selectiveFieldSelectCondition row start limit hblock
                        state index).state.next
                      (selectiveSelectedCode
                        (selectiveFieldSelectCondition row start limit hblock
                          state index).state.selected)
                      (rawCircuitNodeCode (n := descriptionWidth n bound)
                        (.and
                          (selectiveFieldSelectCondition row start limit hblock
                            state index).output value)))) <|
                  max
                    (natBitLength
                      (Nat.pair 0
                        (selectiveWireCode
                          (selectiveFieldSelectGuarded row start limit hblock
                            state index value)))) <|
                    max
                      (natBitLength
                        (selectiveCountCasesSpineCode
                          ((selectiveFieldSelectGuarded row start limit hblock
                            state index value).output :: spine))) <|
                      selectiveFieldSelectForwardBits row start limit hblock
                        (selectiveFieldSelectGuarded row start limit hblock
                          state index value).state (index + 1) rest
                        ((selectiveFieldSelectGuarded row start limit hblock
                          state index value).output :: spine)

-- The forward pass is one induction on the retained values list; its exit
-- emits the base `false` and chains straight into the reverse fold.
private theorem run_selectiveFieldSelectForwardLoop {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) (values : List ℕ)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (spine : List ℕ) (maximumBits : ℕ)
    (hordered : selectiveStateOrdered state)
    (hbits :
      selectiveFieldSelectForwardBits row start limit hblock state index values
        spine ≤ maximumBits)
    (machine : NPOracleState) (hpc : machine.pc = 16)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth n bound)
    (hrowBase : machine.registers 10 = row.val * rowWidth n bound)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hvalues : machine.registers 15 = selectiveCountCasesSpineCode values)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = selectiveCountCasesSpineCode spine) :
    runNPOracleProgram selectiveFieldSelectProgram maximumBits
        (selectiveFieldSelectForwardFuel row start limit hblock state index
          values spine) machine =
      some
        (selectiveWireCode
          (selectiveFieldSelectForwardOutput row start limit hblock state index
            values spine)) := by
  induction values generalizing state index spine machine with
  | nil =>
      have hbitsNil :
          selectiveFieldSelectForwardBits row start limit hblock state index []
              spine =
            max (natBitLength 2)
              (max
                (natBitLength
                  (selectiveEmitInput (state.target - state.next) state.next
                    (selectiveSelectedCode state.selected)
                    (rawCircuitNodeCode (n := descriptionWidth n bound)
                      (.const false))))
                (max
                  (natBitLength
                    (Nat.pair 0
                      (selectiveWireCode (selectiveConst state false))))
                  (natBitLength
                    (selectiveCountCasesFoldWorkBound
                      (selectiveConst state false).state
                      (selectiveConst state false).output spine)))) := rfl
      rw [hbitsNil] at hbits
      have htwoBits := (Nat.le_max_left _ _).trans hbits
      have hbitsTail := (Nat.le_max_right _ _).trans hbits
      have hinputBits := (Nat.le_max_left _ _).trans hbitsTail
      have hbitsTailTwo := (Nat.le_max_right _ _).trans hbitsTail
      have hwireBits := (Nat.le_max_left _ _).trans hbitsTailTwo
      have hfoldBits := (Nat.le_max_right _ _).trans hbitsTailTwo
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        (natBitLength_mono (Nat.zero_le _)).trans htwoBits
      have honeBits : natBitLength 1 ≤ maximumBits :=
        (natBitLength_mono (by omega)).trans htwoBits
      have hnodeCode :
          rawCircuitNodeCode (n := descriptionWidth n bound)
              (.const false) = Nat.pair 0 0 := rfl
      have hemitInput :
          selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.const false)) =
            Nat.pair (selectiveStateCode state)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.const false)) := rfl
      have hcodeBits :
          natBitLength
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.const false)) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hinputBits
        rw [hemitInput]
        exact Nat.right_le_pair _ _
      have hconstOutputBits :
          natBitLength (selectiveConst state false).output ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans
          ((natBitLength_mono (Nat.right_le_pair 0 _)).trans hwireBits)
        exact Nat.right_le_pair _ _
      have hfuel :
          selectiveFieldSelectForwardFuel row start limit hblock state index []
              spine =
            1 +
              (5 +
                (5 +
                  (selectiveEmitFuel (state.target - state.next)
                      (selectiveSelectedCode state.selected) +
                    (7 +
                      (6 +
                        selectiveFieldSelectFoldFuel
                          (selectiveConst state false).state
                          (selectiveConst state false).output
                          spine))))) := rfl
      rw [hfuel, selectiveFieldSelectForwardOutput_nil]
      rw [show 1 + (5 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine))))) =
        (5 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine))))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 16) rfl) hpc]
      rw [if_pos (by rw [hvalues]; rfl)]
      rw [show 5 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine)))) =
        (4 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 34) rfl) rfl hzeroBits]
      rw [show 4 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine)))) =
        (3 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 35) rfl) rfl hzeroBits]
      rw [show 3 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine)))) =
        (2 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine))))) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := descriptionWidth n bound) (.const false))
        (selectiveFieldSelectProgram_controllerAt (pc := 36) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode])
        hcodeBits]
      rw [show 2 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine)))) =
        (1 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 37) rfl) rfl htwoBits]
      rw [show 1 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine)))) =
        (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
            (selectiveConst state false).output spine)))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 38) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveFieldSelectEmitCall state (.const false) hordered
        maximumBits _
        (6 + selectiveFieldSelectFoldFuel (selectiveConst state false).state
          (selectiveConst state false).output spine) _
        (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
        (selectiveCountCasesSpineCode ([] : List ℕ))
        index (selectiveCountCasesSpineCode spine) (machine.registers 18)
        (machine.registers 28) 2 _ rfl hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
      · simp [NPOracleState.write, NPOracleState.jump, hstart]
      · simp [NPOracleState.write, NPOracleState.jump, hlimit]
      · simp [NPOracleState.write, NPOracleState.jump, hvalues,
          selectiveCountCasesSpineCode]
      · simp [NPOracleState.write, NPOracleState.jump, hindex]
      · simp [NPOracleState.write, NPOracleState.jump, hspine]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
          hresumedSelected hresumedOutput hresumedArity _ _ _ _ _ hresumedSpine
          _ _ hresumedPhase
        rw [show 6 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine =
            (5 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 75) rfl) hresumedPc]
        rw [if_neg (by simp [hresumedPhase])]
        rw [show 5 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine =
            (4 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine) + 1 by omega]
        rw [run_decrement_instruction (value := 1)
          (selectiveFieldSelectProgram_controllerAt (pc := 76) rfl) rfl
          (by simp [NPOracleState.jump, hresumedPhase]) honeBits]
        rw [show 4 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine =
            (3 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 77) rfl) rfl]
        rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [show 3 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine =
            (2 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine) + 1 by omega]
        rw [run_decrement_instruction (value := 0)
          (selectiveFieldSelectProgram_controllerAt (pc := 78) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits]
        rw [show 2 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine =
            (1 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 79) rfl) rfl]
        rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [show 1 + selectiveFieldSelectFoldFuel
              (selectiveConst state false).state
              (selectiveConst state false).output spine =
            selectiveFieldSelectFoldFuel (selectiveConst state false).state
              (selectiveConst state false).output spine + 1 by omega]
        rw [run_copy_instruction
          (value := (selectiveConst state false).output)
          (selectiveFieldSelectProgram_controllerAt (pc := 39) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, selectiveConst,
              hresumedOutput])
          hconstOutputBits]
        refine run_selectiveFieldSelectFoldLoop spine
          (selectiveConst state false).state (selectiveConst state false).output
          (selectiveState_emit_ordered state (.const false) hordered)
          maximumBits hfoldBits _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst,
            selectiveWireCode] using hresumedWire
        · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst] using
            hresumedRemaining
        · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst] using
            hresumedNext
        · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst] using
            hresumedSelected
        · simpa [NPOracleState.write, NPOracleState.jump] using hresumedArity
        · simpa [NPOracleState.write, NPOracleState.jump] using hresumedSpine
        · simp [NPOracleState.write, NPOracleState.jump]
  | cons value rest ih =>
      obtain ⟨unaryFuel, hunaryFuel⟩ :
          ∃ fuel,
            selectiveUnaryRunFuel state
                (selectiveUnaryEqualsLiterals (n := n) row start limit index
                  hblock) = fuel := ⟨_, rfl⟩
      obtain ⟨emitFuel, hemitFuel⟩ :
          ∃ fuel,
            selectiveEmitFuel
                ((selectiveFieldSelectCondition row start limit hblock state index).state.target -
                  (selectiveFieldSelectCondition row start limit hblock state index).state.next)
                (selectiveSelectedCode
                  (selectiveFieldSelectCondition row start limit hblock state
                    index).state.selected) = fuel := ⟨_, rfl⟩
      obtain ⟨recFuel, hrecFuel⟩ :
          ∃ fuel,
            selectiveFieldSelectForwardFuel row start limit hblock
                (selectiveFieldSelectGuarded row start limit hblock state index value).state (index
                  + 1) rest
                ((selectiveFieldSelectGuarded row start limit hblock state index value).output ::
                  spine) = fuel := ⟨_, rfl⟩
      have hfuel :
          selectiveFieldSelectForwardFuel row start limit hblock state index
              (value :: rest) spine =
            6 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) := by
        rw [← hunaryFuel, ← hemitFuel, ← hrecFuel]
        rfl
      have hbitsCons :
          selectiveFieldSelectForwardBits row start limit hblock state index
              (value :: rest) spine =
            max
              (selectiveUnaryRunBits state
                (selectiveUnaryEqualsLiterals (n := n) row start limit index
                  hblock) (row.val * rowWidth n bound) start index)
              (max
                (natBitLength
                  (selectiveUnaryInput (selectiveStateCode state)
                    (descriptionWidth n bound) (row.val * rowWidth n bound) start limit index))
                (max
                  (natBitLength
                    (Nat.pair 0 (selectiveWireCode (selectiveFieldSelectCondition row start limit
                      hblock state index))))
                  (max
                    (natBitLength
                      (selectiveCountCasesSpineCode (value :: rest)))
                    (max (natBitLength (index + 1))
                      (max
                        (natBitLength
                          (selectiveEmitInput
                            ((selectiveFieldSelectCondition row start limit hblock state
                              index).state.target -
                              (selectiveFieldSelectCondition row start limit hblock state
                                index).state.next)
                            (selectiveFieldSelectCondition row start limit hblock state
                              index).state.next
                            (selectiveSelectedCode
                              (selectiveFieldSelectCondition row start limit hblock state
                                index).state.selected)
                            (rawCircuitNodeCode (n := descriptionWidth n bound)
                              (.and (selectiveFieldSelectCondition row start limit hblock state
                                index).output value))))
                        (max
                          (natBitLength
                            (Nat.pair 0 (selectiveWireCode (selectiveFieldSelectGuarded row start
                              limit hblock state index value))))
                          (max
                            (natBitLength
                              (selectiveCountCasesSpineCode
                                ((selectiveFieldSelectGuarded row start limit hblock state index
                                  value).output :: spine)))
                            (selectiveFieldSelectForwardBits row start limit
                              hblock (selectiveFieldSelectGuarded row start limit hblock state
                                index value).state (index + 1) rest
                              ((selectiveFieldSelectGuarded row start limit hblock state index
                                value).output :: spine))))))))) := rfl
      rw [hbitsCons] at hbits
      have hcalleeBits := (Nat.le_max_left _ _).trans hbits
      have hbitsOne := (Nat.le_max_right _ _).trans hbits
      have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
      have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
      have hcondWireBits := (Nat.le_max_left _ _).trans hbitsTwo
      have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
      have hvaluesConsBits := (Nat.le_max_left _ _).trans hbitsThree
      have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
      have hindexBits := (Nat.le_max_left _ _).trans hbitsFour
      have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
      have hemitInputBits := (Nat.le_max_left _ _).trans hbitsFive
      have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
      have hguardWireBits := (Nat.le_max_left _ _).trans hbitsSix
      have hbitsSeven := (Nat.le_max_right _ _).trans hbitsSix
      have hnewSpineBits := (Nat.le_max_left _ _).trans hbitsSeven
      have hrecBits := (Nat.le_max_right _ _).trans hbitsSeven
      have hvaluesForm :
          selectiveCountCasesSpineCode (value :: rest) =
            Nat.pair 1
              (Nat.pair value (selectiveCountCasesSpineCode rest)) := rfl
      have hconsBits :
          natBitLength (Nat.pair value (selectiveCountCasesSpineCode rest)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hvaluesConsBits
        rw [hvaluesForm]
        exact Nat.right_le_pair 1 _
      have hvalueBits : natBitLength value ≤ maximumBits :=
        (natBitLength_mono (Nat.left_le_pair _ _)).trans hconsBits
      have htailValuesBits :
          natBitLength (selectiveCountCasesSpineCode rest) ≤ maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans hconsBits
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        (natBitLength_mono (Nat.zero_le _)).trans hvaluesConsBits
      have hnodeCode :
          rawCircuitNodeCode (n := descriptionWidth n bound)
              (.and (selectiveFieldSelectCondition row start limit hblock state index).output
                value) =
            Nat.pair 3
              (Nat.pair (descriptionWidth n bound + (selectiveFieldSelectCondition row start limit
                hblock state index).output)
                (descriptionWidth n bound + value)) := rfl
      have hemitInputForm :
          selectiveEmitInput
              ((selectiveFieldSelectCondition row start limit hblock state index).state.target -
                (selectiveFieldSelectCondition row start limit hblock state index).state.next)
              (selectiveFieldSelectCondition row start limit hblock state index).state.next
              (selectiveSelectedCode (selectiveFieldSelectCondition row start limit hblock state
                index).state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.and (selectiveFieldSelectCondition row start limit hblock state index).output
                  value)) =
            Nat.pair (selectiveStateCode (selectiveFieldSelectCondition row start limit hblock
              state index).state)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.and (selectiveFieldSelectCondition row start limit hblock state index).output
                  value)) := rfl
      have hcodeBits :
          natBitLength
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.and (selectiveFieldSelectCondition row start limit hblock state index).output
                  value)) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hemitInputBits
        rw [hemitInputForm]
        exact Nat.right_le_pair _ _
      have hthreeBits : natBitLength 3 ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hcodeBits
        rw [hnodeCode]
        exact Nat.left_le_pair 3 _
      have honeBits : natBitLength 1 ≤ maximumBits :=
        (natBitLength_mono (by omega)).trans hthreeBits
      have hchildrenBits :
          natBitLength
              (Nat.pair (descriptionWidth n bound + (selectiveFieldSelectCondition row start limit
                hblock state index).output)
                (descriptionWidth n bound + value)) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hcodeBits
        rw [hnodeCode]
        exact Nat.right_le_pair 3 _
      have hleftChildBits :
          natBitLength (descriptionWidth n bound + (selectiveFieldSelectCondition row start limit
            hblock state index).output) ≤ maximumBits :=
        (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
      have hrightChildBits :
          natBitLength (descriptionWidth n bound + value) ≤ maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
      have hnewSpineForm :
          selectiveCountCasesSpineCode ((selectiveFieldSelectGuarded row start limit hblock state
            index value).output :: spine) =
            Nat.pair 1
              (Nat.pair (selectiveFieldSelectGuarded row start limit hblock state index
                value).output
                (selectiveCountCasesSpineCode spine)) := rfl
      have hspinePairBits :
          natBitLength
              (Nat.pair (selectiveFieldSelectGuarded row start limit hblock state index
                value).output
                (selectiveCountCasesSpineCode spine)) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hnewSpineBits
        rw [hnewSpineForm]
        exact Nat.right_le_pair 1 _
      have hvaluesNonzero : machine.registers 15 ≠ 0 := by
        rw [hvalues, hvaluesForm]
        have hone :=
          Nat.left_le_pair 1
            (Nat.pair value (selectiveCountCasesSpineCode rest))
        omega
      rw [hfuel, selectiveFieldSelectForwardOutput_cons]
      rw [show 6 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) =
        (5 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) ) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 16) rfl) hpc]
      rw [if_neg hvaluesNonzero]
      rw [show 5 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) =
        (4 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) ) + 1 by omega]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (selectiveCountCasesSpineCode rest))
        (selectiveFieldSelectProgram_controllerAt (pc := 17) rfl) rfl
        (by simp [NPOracleState.jump, hvalues, hvaluesForm]) hconsBits]
      rw [show 4 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) =
        (3 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) ) + 1 by omega]
      rw [run_unpairLeft_instruction (value := value)
        (selectiveFieldSelectProgram_controllerAt (pc := 18) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      rw [show 3 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) =
        (2 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) ) + 1 by omega]
      rw [run_unpairRight_instruction
        (value := selectiveCountCasesSpineCode rest)
        (selectiveFieldSelectProgram_controllerAt (pc := 19) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) htailValuesBits]
      rw [show 2 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) =
        (1 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) ) + 1 by omega]
      rw [run_set_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 20) rfl) rfl
        hzeroBits]
      rw [show 1 + (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) =
        (9 + (unaryFuel + (7 + (1 + (7 + (5 + (emitFuel +
              (7 + (3 + (5 + recFuel)))))))))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFieldSelectProgram_controllerAt (pc := 21) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveFieldSelectUnaryCall state row start limit index
        hblock hordered maximumBits unaryFuel
        (1 + (7 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))))) _
        (selectiveCountCasesSpineCode rest)
        (selectiveCountCasesSpineCode spine) value (machine.registers 28) 0 _
        hunaryFuel.symm hcalleeBits hrequestBits hcondWireBits ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
      · simp [NPOracleState.write, NPOracleState.jump, hstart]
      · simp [NPOracleState.write, NPOracleState.jump, hlimit]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, hindex]
      · simp [NPOracleState.write, NPOracleState.jump, hspine]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedRemaining hresumedNext
          hresumedSelected hresumedOutput hresumedArity hresumedRowBase
          hresumedStart hresumedLimit hresumedValues hresumedIndex
          hresumedSpine hresumedHead hresumedAccumulated hresumedPhase
        rw [show 1 + (7 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) =
          (7 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 75) rfl)
          hresumedPc]
        rw [if_pos hresumedPhase]
        rw [show 7 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (6 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_add_instruction
          (value := descriptionWidth n bound + (selectiveFieldSelectCondition row start limit
            hblock state index).output)
          (selectiveFieldSelectProgram_controllerAt (pc := 22) rfl) rfl
          (by
            simp [NPOracleState.jump, hresumedArity, hresumedOutput])
          hleftChildBits]
        rw [show 6 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (5 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_add_instruction (value := descriptionWidth n bound + value)
          (selectiveFieldSelectProgram_controllerAt (pc := 23) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, hresumedArity,
              hresumedHead])
          hrightChildBits]
        rw [show 5 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (4 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_pair_instruction
          (value :=
            Nat.pair (descriptionWidth n bound + (selectiveFieldSelectCondition row start limit
              hblock state index).output) (descriptionWidth n bound + value))
          (selectiveFieldSelectProgram_controllerAt (pc := 24) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
        rw [show 4 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (3 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_set_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 25) rfl) rfl
          hthreeBits]
        rw [show 3 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (2 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_pair_instruction
          (value :=
            rawCircuitNodeCode (n := descriptionWidth n bound)
              (.and (selectiveFieldSelectCondition row start limit hblock state index).output
                value))
          (selectiveFieldSelectProgram_controllerAt (pc := 26) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode])
          hcodeBits]
        rw [show 2 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (1 + (5 + (emitFuel + (7 + (3 + (5 + recFuel)))))) + 1 by omega]
        rw [run_set_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 27) rfl) rfl
          honeBits]
        rw [show 1 + (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) =
          (5 + (emitFuel + (7 + (3 + (5 + recFuel))))) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFieldSelectProgram_controllerAt (pc := 28) rfl) rfl]
        simp only [ite_self]
        refine run_selectiveFieldSelectEmitCall
          (selectiveFieldSelectCondition row start limit hblock state index).state
          (.and (selectiveFieldSelectCondition row start limit hblock state index).output value)
          (selectiveFieldSelectCondition_ordered row start limit hblock state
            index hordered)
          maximumBits emitFuel (3 + (5 + recFuel)) _ (descriptionWidth n bound)
          (row.val * rowWidth n bound) start limit
          (selectiveCountCasesSpineCode rest) index
          (selectiveCountCasesSpineCode spine) value (machine.registers 28) 1 _
          hemitFuel.symm hemitInputBits hguardWireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rfl
        · simp [NPOracleState.write, NPOracleState.jump, hresumedRemaining]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedNext]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedSelected]
        · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedArity]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedRowBase]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedStart]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedLimit]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedValues]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedIndex]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedSpine]
        · simp [NPOracleState.write, NPOracleState.jump, hresumedHead]
        · simpa [NPOracleState.write, NPOracleState.jump] using
            hresumedAccumulated
        · simp [NPOracleState.write, NPOracleState.jump]
        · intro final hfinalPc _ hfinalRemaining hfinalNext hfinalSelected
            hfinalOutput hfinalArity hfinalRowBase hfinalStart hfinalLimit
            hfinalValues hfinalIndex hfinalSpine _ _ hfinalPhase
          rw [show 3 + (5 + recFuel) = (2 + (5 + recFuel)) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveFieldSelectProgram_controllerAt (pc := 75) rfl)
            hfinalPc]
          rw [if_neg (by simp [hfinalPhase])]
          rw [show 2 + (5 + recFuel) = (1 + (5 + recFuel)) + 1 by omega]
          rw [run_decrement_instruction (value := 0)
            (selectiveFieldSelectProgram_controllerAt (pc := 76) rfl) rfl
            (by simp [NPOracleState.jump, hfinalPhase]) hzeroBits]
          rw [show 1 + (5 + recFuel) = (5 + recFuel) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveFieldSelectProgram_controllerAt (pc := 77) rfl) rfl]
          rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [show 5 + recFuel = (4 + recFuel) + 1 by omega]
          rw [run_pair_instruction
            (value :=
              Nat.pair (selectiveFieldSelectGuarded row start limit hblock state index value).output
                (selectiveCountCasesSpineCode spine))
            (selectiveFieldSelectProgram_controllerAt (pc := 29) rfl) rfl
            (by
              simp [NPOracleState.write, NPOracleState.jump,
                selectiveFieldSelectGuarded, selectiveAnd, hfinalOutput,
                hfinalSpine])
            hspinePairBits]
          rw [show 4 + recFuel = (3 + recFuel) + 1 by omega]
          rw [run_set_instruction
            (selectiveFieldSelectProgram_controllerAt (pc := 30) rfl) rfl
            honeBits]
          rw [show 3 + recFuel = (2 + recFuel) + 1 by omega]
          rw [run_pair_instruction
            (value :=
              selectiveCountCasesSpineCode
                ((selectiveFieldSelectGuarded row start limit hblock state index value).output ::
                  spine))
            (selectiveFieldSelectProgram_controllerAt (pc := 31) rfl) rfl
            (by
              simp [NPOracleState.write, NPOracleState.jump, hnewSpineForm])
            hnewSpineBits]
          rw [show 2 + recFuel = (1 + recFuel) + 1 by omega]
          rw [run_increment_instruction (value := index + 1)
            (selectiveFieldSelectProgram_controllerAt (pc := 32) rfl) rfl
            (by
              simp [NPOracleState.write, NPOracleState.jump, hfinalIndex])
            hindexBits]
          rw [show 1 + recFuel = recFuel + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveFieldSelectProgram_controllerAt (pc := 33) rfl) rfl]
          simp only [ite_self]
          rw [← hrecFuel]
          refine ih (selectiveFieldSelectGuarded row start limit hblock state index value).state
            (index + 1)
            ((selectiveFieldSelectGuarded row start limit hblock state index value).output :: spine)
            (selectiveFieldSelectGuarded_ordered row start limit hblock state
              index value hordered)
            hrecBits _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          · simpa [NPOracleState.write, NPOracleState.jump,
              selectiveFieldSelectGuarded, selectiveAnd] using hfinalRemaining
          · simpa [NPOracleState.write, NPOracleState.jump,
              selectiveFieldSelectGuarded, selectiveAnd] using hfinalNext
          · simpa [NPOracleState.write, NPOracleState.jump,
              selectiveFieldSelectGuarded, selectiveAnd] using hfinalSelected
          · simpa [NPOracleState.write, NPOracleState.jump] using hfinalArity
          · simpa [NPOracleState.write, NPOracleState.jump] using
              hfinalRowBase
          · simpa [NPOracleState.write, NPOracleState.jump] using hfinalStart
          · simpa [NPOracleState.write, NPOracleState.jump] using hfinalLimit
          · simpa [NPOracleState.write, NPOracleState.jump] using hfinalValues
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 6. The level premise, discharged

The request parser feeds the choice loop head; §6 assembles the whole run and
packages it as the runner structure the callers one level up consume. -/

private theorem selectiveFieldSelectForwardOutput_nil_spine {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (values : List ℕ) :
    selectiveFieldSelectForwardOutput row start limit hblock state index values
        [] =
      selectiveCompileGuardedAny state
        (selectiveFieldSelectChoices row start limit hblock index values) := by
  rw [selectiveCompileGuardedAny_eq_fold]
  simp only [selectiveFieldSelectForwardOutput, List.append_nil]

theorem selectiveCountCasesSpineCode_eq_encodeTaggedList (values : List ℕ) :
    selectiveCountCasesSpineCode values = encodeTaggedList values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [selectiveCountCasesSpineCode, encodeTaggedList, ih]

/-- Interpreter fuel of one whole guarded selection: sixteen parser steps and
the choice loop. -/
def selectiveFieldSelectRunFuel {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (values : List ℕ) :
    ℕ :=
  16 + selectiveFieldSelectForwardFuel row start limit hblock state 0 values []

/-- Register-width envelope of one whole guarded selection. -/
def selectiveFieldSelectRunBits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (values : List ℕ) :
    ℕ :=
  max
    (natBitLength
      (selectiveFieldSelectInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
        (selectiveCountCasesSpineCode values)))
    (selectiveFieldSelectForwardBits row start limit hblock state 0 values [])

/-- **The field selector's run.**  The `196`-instruction stream started on its
own ABI frame, at any entry registers, returns exactly the compiler wire the
source compiler produces for the guarded disjunction of the scheduled
choices. -/
theorem run_selectiveFieldSelectProgram {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit : ℕ) (values : List ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveFieldSelectInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
          (selectiveCountCasesSpineCode values)) :
    runNPOracleProgram selectiveFieldSelectProgram
        (selectiveFieldSelectRunBits row start limit hblock state values)
        (selectiveFieldSelectRunFuel row start limit hblock state values)
        entry =
      some
        (selectiveWireCode
          (selectiveCompileGuardedAny state
            (selectiveFieldSelectChoices row start limit hblock 0
              values))) := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hrequestBits :
      natBitLength
          (selectiveFieldSelectInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
            (selectiveCountCasesSpineCode values)) ≤
        selectiveFieldSelectRunBits row start limit hblock state values :=
    Nat.le_max_left _ _
  have hforwardBits :
      selectiveFieldSelectForwardBits row start limit hblock state 0 values
          [] ≤
        selectiveFieldSelectRunBits row start limit hblock state values :=
    Nat.le_max_right _ _
  have hflat := hrequestBits
  simp only [selectiveFieldSelectInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have hrowBaseBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hstartBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hlimitBits := natBitLength_pair_left hfour
  have hvaluesBits := natBitLength_pair_right hfour
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left hnextSelectedBits
  have hselectedBits := natBitLength_pair_right hnextSelectedBits
  have hzeroBits :
      natBitLength 0 ≤
        selectiveFieldSelectRunBits row start limit hblock state values :=
    (natBitLength_mono (Nat.zero_le _)).trans hvaluesBits
  rw [← selectiveFieldSelectForwardOutput_nil_spine]
  rw [selectiveFieldSelectRunFuel]
  rw [show 16 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (15 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveFieldSelectProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, selectiveFieldSelectInput])
    hstateBits]
  rw [show 15 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (14 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair (descriptionWidth n bound) <|
      Nat.pair (row.val * rowWidth n bound) <|
        Nat.pair start
          (Nat.pair limit (selectiveCountCasesSpineCode values)))
    (selectiveFieldSelectProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveFieldSelectInput])
    hone]
  rw [show 14 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (13 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveFieldSelectProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 13 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (12 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair state.next (selectiveSelectedCode
    state.selected))
    (selectiveFieldSelectProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hnextSelectedBits]
  rw [show 12 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (11 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveFieldSelectProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hnextBits]
  rw [show 11 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (10 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveSelectedCode state.selected)
    (selectiveFieldSelectProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hselectedBits]
  rw [show 10 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (9 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := descriptionWidth n bound)
    (selectiveFieldSelectProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [show 9 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (8 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair (row.val * rowWidth n bound) <|
      Nat.pair start (Nat.pair limit (selectiveCountCasesSpineCode values)))
    (selectiveFieldSelectProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htwo]
  rw [show 8 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (7 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := row.val * rowWidth n bound)
    (selectiveFieldSelectProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrowBaseBits]
  rw [show 7 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (6 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair start (Nat.pair limit
    (selectiveCountCasesSpineCode values)))
    (selectiveFieldSelectProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hthree]
  rw [show 6 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (5 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := start)
    (selectiveFieldSelectProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hstartBits]
  rw [show 5 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (4 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (selectiveCountCasesSpineCode values))
    (selectiveFieldSelectProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hfour]
  rw [show 4 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (3 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairLeft_instruction (value := limit)
    (selectiveFieldSelectProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hlimitBits]
  rw [show 3 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (2 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveCountCasesSpineCode values)
    (selectiveFieldSelectProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hvaluesBits]
  rw [show 2 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (1 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values [])) + 1 by omega]
  rw [run_set_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 14) rfl) rfl hzeroBits]
  rw [show 1 + (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) =
    (selectiveFieldSelectForwardFuel row start limit hblock state 0 values []) + 1 by omega]
  rw [run_set_instruction
    (selectiveFieldSelectProgram_controllerAt (pc := 15) rfl) rfl hzeroBits]
  refine run_selectiveFieldSelectForwardLoop row start limit hblock values
    state 0 [] _ hordered hforwardBits _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump,
      selectiveCountCasesSpineCode]

/-- **Level premise.**  The field selector compiles one guarded selection over
a description row at its own ABI frame, at an arbitrary entry state, with
resources depending on the request alone. -/
structure SelectiveFieldSelectRunner (width bound : ℕ) where
  bits : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    ∀ start limit : ℕ, start + limit ≤ rowWidth width bound → List ℕ → ℕ
  fuel : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    ∀ start limit : ℕ, start + limit ≤ rowWidth width bound → List ℕ → ℕ
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (row : Fin (bound + 1)) (start limit : ℕ) (values : List ℕ)
      (hblock : start + limit ≤ rowWidth width bound),
      selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveFieldSelectInput (selectiveStateCode state)
        (descriptionWidth width bound) (row.val * rowWidth width bound) start
        limit (encodeTaggedList values) →
    runNPOracleProgram selectiveFieldSelectProgram
        (bits state row start limit hblock values)
        (fuel state row start limit hblock values) entry =
      some
        (selectiveWireCode
          (selectiveCompileFieldSelect state
            (fun candidate value =>
              unaryEqualsExpr candidate start limit value hblock) row values))

/-- **Level premise, discharged.**  The field selector's run at its own ABI
frame, packaged in the runner shape the callers one level up consume.  Nothing
on this level is left as a premise. -/
def selectiveFieldSelectRunner (width bound : ℕ) :
    SelectiveFieldSelectRunner width bound where
  bits state row start limit hblock values :=
    selectiveFieldSelectRunBits row start limit hblock state values
  fuel state row start limit hblock values :=
    selectiveFieldSelectRunFuel row start limit hblock state values
  executes := by
    intro state row start limit values hblock hordered entry hentryPc
      hentryInput
    have hchoices :
        selectiveCompileFieldSelect state
            (fun candidate value =>
              unaryEqualsExpr candidate start limit value hblock) row values =
          selectiveCompileGuardedAny state
            (selectiveFieldSelectChoices row start limit hblock 0 values) := by
      rw [selectiveFieldSelectChoices_eq_zipIdx]
      rfl
    rw [hchoices]
    refine run_selectiveFieldSelectProgram state row start limit values hblock
      hordered entry hentryPc ?_
    rw [hentryInput, selectiveCountCasesSpineCode_eq_encodeTaggedList]

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
