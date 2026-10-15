import Proof.Supplier.SelectiveAddressSelectRun

/-!
# The grammar-case compiler's schedule and call frames

`selectiveGrammarCaseProgram` is the `446`-instruction stream that compiles one
of the seven grammar row cases: a controller of `136` instructions with three
relocated callees, the `97`-instruction unary-equality compiler, the
`195`-instruction address selector, and the `18`-instruction append transition.

Every case has exactly three top-level conjuncts.  A small dispatcher chooses
the middle and last field predicate from the case tag; one unary callee, one
address callee and one append kernel implement the complete shared schedule.
This module fixes that typed schedule (§1), decodes the fixed stream (§2), and
proves the three shared call frames (§3) — the call sites through which every
trace on this level passes.  §5–§9 then execute the whole stream: the all-ones
address word (§5), the seven-way forward dispatcher (§6), the retained spine and
the loop exit (§7), the reverse `and` fold (§8) and the request parser (§9).
The level's runner premise (§4) is discharged at the end of §9.
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
open NearCubicWires.VerifiedLinker

open private selectiveGrammarCaseInput selectiveGrammarCaseControllerProgram
  selectiveGrammarCaseControllerProgram_length selectiveGrammarCaseProgram
  selectiveGrammarCaseProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

open private selectiveAddressSelectProgram
  selectiveAddressSelectProgram_length selectiveAddressSelectInput from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The three conjuncts of one grammar row case, at the typed level

The dispatcher at `30`–`35` and `53`–`62` selects the middle and last field
predicate from the case tag alone; the first conjunct is always the row's tag
test.  §1 names that schedule and identifies it with the source compiler's own
five node-row cases, its output row and its padding row. -/

/-- The middle conjunct of one grammar row case. -/
def selectiveGrammarCaseFirstField {n bound : ℕ}
    (row : Fin (bound + 1)) (rowIndex caseTag : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  if caseTag = 0 then firstFieldLessExpr row 2
  else if caseTag = 1 then firstFieldLessExpr row n
  else if 6 ≤ caseTag then firstFieldEqualsExpr row 0
  else firstFieldLessExpr row rowIndex

/-- The last conjunct of one grammar row case. -/
def selectiveGrammarCaseSecondField {n bound : ℕ}
    (row : Fin (bound + 1)) (rowIndex caseTag : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  if caseTag = 3 ∨ caseTag = 4 then secondFieldLessExpr row rowIndex
  else secondFieldEqualsExpr row 0

/-- The conjunct schedule the controller walks. -/
def selectiveGrammarCaseConjuncts {n bound : ℕ}
    (row : Fin (bound + 1)) (rowIndex caseTag : ℕ) :
    List (BoolExpr (descriptionWidth n bound)) :=
  [tagEqualsExpr row caseTag,
    selectiveGrammarCaseFirstField (n := n) row rowIndex caseTag,
    selectiveGrammarCaseSecondField (n := n) row rowIndex caseTag]

/-- The compiled wire of one grammar row case. -/
def selectiveGrammarCaseExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (rowIndex caseTag : ℕ) :
    BoolExpr (descriptionWidth n bound) :=
  BoolExpr.all (selectiveGrammarCaseConjuncts (n := n) row rowIndex caseTag)

private theorem firstFieldLessExpr_eq_ofFn {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ) :
    firstFieldLessExpr (n := n) row upper =
      BoolExpr.any
        (List.ofFn fun index : Fin upper =>
          firstFieldEqualsExpr (n := n) row index.val) := by
  rw [firstFieldLessExpr]
  refine congrArg BoolExpr.any ?_
  refine List.ext_getElem (by simp) ?_
  intro index hleft hright
  simp

/-- The address callee's all-ones request compiles exactly the source
compiler's bounded first-field test. -/
theorem constantAddressSelectionExpr_ones_eq_firstFieldLess {n bound : ℕ}
    (row : Fin (bound + 1)) (address : BitInput n)
    (hones : ∀ index : Fin n, address index = true) :
    constantAddressSelectionExpr (n := n) row address =
      firstFieldLessExpr (n := n) row n := by
  rw [firstFieldLessExpr_eq_ofFn, constantAddressSelectionExpr]
  refine congrArg BoolExpr.any (congrArg List.ofFn (funext ?_))
  intro index
  rw [hones index]
  rfl

/-- **The controller's schedule, identified with the source compiler's node
rows.**  The five node-row cases, the output row and the padding row are
exactly the seven case tags of this controller. -/
theorem selectiveGrammarCaseExpr_eq_nodeRow {n bound : ℕ}
    (row : Fin (bound + 1)) (caseTag : ℕ) (hcase : caseTag < 5) :
    selectiveGrammarCaseExpr (n := n) row row.val caseTag =
      BoolExpr.all
        [tagEqualsExpr row caseTag,
          selectiveGrammarCaseFirstField (n := n) row row.val caseTag,
          selectiveGrammarCaseSecondField (n := n) row row.val caseTag] := by
  cases hcase
  all_goals rfl

theorem selectiveGrammarCaseExpr_five {n bound : ℕ}
    (row : Fin (bound + 1)) :
    selectiveGrammarCaseExpr (n := n) row row.val 5 =
      outputRowExpr (n := n) row := by
  simp only [selectiveGrammarCaseExpr, selectiveGrammarCaseConjuncts,
    selectiveGrammarCaseFirstField, selectiveGrammarCaseSecondField,
    outputRowExpr]
  norm_num

theorem selectiveGrammarCaseExpr_six {n bound : ℕ}
    (row : Fin (bound + 1)) :
    selectiveGrammarCaseExpr (n := n) row row.val 6 =
      paddingRowExpr (n := n) row := by
  simp only [selectiveGrammarCaseExpr, selectiveGrammarCaseConjuncts,
    selectiveGrammarCaseFirstField, selectiveGrammarCaseSecondField,
    paddingRowExpr]
  norm_num

/-- **The controller's scheduling identity.**  The compiled case is the forward
conjunct pass followed by the reverse `and` fold over the retained spine — the
identity already proved for the unary controller, instantiated at this
level's three conjuncts. -/
theorem selectiveGrammarCaseExpr_eq_fold {n bound : ℕ}
    (row : Fin (bound + 1)) (rowIndex caseTag : ℕ)
    (state : SelectiveState (descriptionWidth n bound)) :
    selectiveCompileExpr state
        (selectiveGrammarCaseExpr (n := n) row rowIndex caseTag) =
      selectiveUnaryFold
        (selectiveConst
          (selectiveUnaryHeads state
            (selectiveGrammarCaseConjuncts (n := n) row rowIndex
              caseTag)).state true).state
        (selectiveConst
          (selectiveUnaryHeads state
            (selectiveGrammarCaseConjuncts (n := n) row rowIndex
              caseTag)).state true).output
        (selectiveUnaryHeads state
          (selectiveGrammarCaseConjuncts (n := n) row rowIndex
            caseTag)).values.reverse :=
  selectiveCompileExpr_all_eq_fold _ state

theorem selectiveGrammarCaseExpr_ordered {n bound : ℕ}
    (row : Fin (bound + 1)) (rowIndex caseTag : ℕ)
    (state : SelectiveState (descriptionWidth n bound))
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileExpr state
        (selectiveGrammarCaseExpr (n := n) row rowIndex caseTag)).state :=
  selectiveCompileExpr_ordered state _ hordered

/-! ## 2. Decoding the fixed 446-instruction stream

The controller occupies the first `136` positions, the unary callee the next
`97`, the address callee the next `195`, and the append callee the last `18`.
Every later step decodes through exactly one of the four lemmas below. -/

theorem selectiveGrammarCaseProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveGrammarCaseControllerProgram 136 233 428)[pc]? =
        some instruction) :
    selectiveGrammarCaseProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveGrammarCaseControllerProgram 136 233 428).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveGrammarCaseControllerProgram_length] at hpc
  simp only [selectiveGrammarCaseProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length, selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveGrammarCaseControllerProgram_length]
    omega)]
  exact hlookup

theorem selectiveGrammarCaseProgram_unaryCallable :
    ProgramCallableAt selectiveGrammarCaseProgram selectiveUnaryProgram
      136 1000 50 97 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUnaryProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUnaryProgram_length] at hpc
  simp only [selectiveGrammarCaseProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length, selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveGrammarCaseControllerProgram_length]
    omega)]
  simp only [selectiveGrammarCaseControllerProgram_length]
  rw [show 136 + pc - 136 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveGrammarCaseProgram_addressCallable :
    ProgramCallableAt selectiveGrammarCaseProgram selectiveAddressSelectProgram
      233 5000 50 97 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveAddressSelectProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveAddressSelectProgram_length] at hpc
  simp only [selectiveGrammarCaseProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length, selectiveAddressSelectProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveGrammarCaseControllerProgram_length, selectiveUnaryProgram_length]
  rw [show 233 + pc - (136 + 97) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveGrammarCaseProgram_emitCallable :
    ProgramCallableAt selectiveGrammarCaseProgram selectiveEmitProgram
      428 10000 50 118 := by
  intro pc instruction hlookup
  simp only [selectiveGrammarCaseProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveGrammarCaseControllerProgram_length,
      selectiveUnaryProgram_length, selectiveAddressSelectProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveGrammarCaseControllerProgram_length, selectiveUnaryProgram_length,
    selectiveAddressSelectProgram_length]
  rw [show 428 + pc - (136 + 97 + 195) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The three shared call frames

Every append site reaches the relocated append through the physical block at
`113`; every unary site reaches the relocated unary compiler through the block
at `88`; every address site reaches the relocated address selector through the
block at `78`.  Each block builds the callee's request from the live state
registers, runs the callee, and unpacks the returned wire back into those
registers. -/

private theorem run_selectiveGrammarCaseEmitCall {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity rowBase fieldLimit width rowIndex caseTag counter spine sixPlusLimit six : ℕ)
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
    (hpc : machine.pc = 113)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 23 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hrowBase : machine.registers 10 = rowBase)
    (hfieldLimit : machine.registers 12 = fieldLimit)
    (hwidth : machine.registers 14 = width)
    (hrowIndex : machine.registers 16 = rowIndex)
    (hcaseTag : machine.registers 17 = caseTag)
    (hcounter : machine.registers 18 = counter)
    (hspine : machine.registers 22 = spine)
    (hsixPlusLimit : machine.registers 38 = sixPlusLimit)
    (hsix : machine.registers 40 = six)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 125 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 20 = (state.emit node).output →
      resumed.registers 8 = arity →
      resumed.registers 10 = rowBase →
      resumed.registers 12 = fieldLimit →
      resumed.registers 14 = width →
      resumed.registers 16 = rowIndex →
      resumed.registers 17 = caseTag →
      resumed.registers 18 = counter →
      resumed.registers 22 = spine →
      resumed.registers 38 = sixPlusLimit →
      resumed.registers 40 = six →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
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
  have hcompiledStateBits := natBitLength_pair_left hwireParts
  have hcompiledOutputBits := natBitLength_pair_right hwireParts
  have hcompiledStateFlat := hcompiledStateBits
  rw [hstateForm] at hcompiledStateFlat
  have hcompiledRemainingBits := natBitLength_pair_left hcompiledStateFlat
  have hcompiledTailBits := natBitLength_pair_right hcompiledStateFlat
  have hcompiledNextBits := natBitLength_pair_left hcompiledTailBits
  have hcompiledSelectedBits := natBitLength_pair_right hcompiledTailBits
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
    (selectiveGrammarCaseProgram_controllerAt (pc := 113) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveGrammarCaseProgram_controllerAt (pc := 114) rfl) rfl
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
    (selectiveGrammarCaseProgram_controllerAt (pc := 115) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 116) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 117) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveGrammarCaseProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state node hordered frame hframePc ?_)
      hemitCalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _emitHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode (state.emit node))
      (selectiveGrammarCaseProgram_controllerAt (pc := 118) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := selectiveStateCode (state.emit node).state)
      (selectiveGrammarCaseProgram_controllerAt (pc := 119) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveGrammarCaseProgram_controllerAt (pc := 120) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := ((state.emit node).state).target - ((state.emit node).state).next)
      (selectiveGrammarCaseProgram_controllerAt (pc := 121) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair ((state.emit node).state).next
          (selectiveSelectedCode ((state.emit node).state).selected))
      (selectiveGrammarCaseProgram_controllerAt (pc := 122) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := ((state.emit node).state).next)
      (selectiveGrammarCaseProgram_controllerAt (pc := 123) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode ((state.emit node).state).selected)
      (selectiveGrammarCaseProgram_controllerAt (pc := 124) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState,
        harity, hrowBase, hfieldLimit, hwidth, hrowIndex, hcaseTag, hcounter, hspine,
          hsixPlusLimit, hsix]

private theorem run_selectiveGrammarCaseUnaryCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (maximumBits unaryFuel extraFuel finalOutput : ℕ)
    (fieldLimit width rowIndex caseTag counter spine sixPlusLimit six : ℕ)
    (machine : NPOracleState)
    (hunaryFuel :
      unaryFuel =
        selectiveUnaryRunFuel state
          (selectiveUnaryEqualsLiterals (n := n) row start limit value hblock))
    (hcalleeBits :
      selectiveUnaryRunBits state
          (selectiveUnaryEqualsLiterals (n := n) row start limit value hblock)
          (row.val * rowWidth n bound) start value ≤
        maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveUnaryInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound) start
            limit value) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode (selectiveCompileExpr state (unaryEqualsExpr (n
        := n) row start limit value hblock)))) ≤ maximumBits)
    (hpc : machine.pc = 88)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth n bound)
    (hrowBase : machine.registers 10 = row.val * rowWidth n bound)
    (hstart : machine.registers 35 = start)
    (hlimit : machine.registers 36 = limit)
    (hvalue : machine.registers 37 = value)
    (hfieldLimit : machine.registers 12 = fieldLimit)
    (hwidth : machine.registers 14 = width)
    (hrowIndex : machine.registers 16 = rowIndex)
    (hcaseTag : machine.registers 17 = caseTag)
    (hcounter : machine.registers 18 = counter)
    (hspine : machine.registers 22 = spine)
    (hsixPlusLimit : machine.registers 38 = sixPlusLimit)
    (hsix : machine.registers 40 = six)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 104 →
      resumed.registers 4 = ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
        value hblock))).state.target - ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row
        start limit value hblock))).state.next →
      resumed.registers 6 = ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
        value hblock))).state.next →
      resumed.registers 7 =
        selectiveSelectedCode ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start
          limit value hblock))).state.selected →
      resumed.registers 20 = ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
        value hblock))).output →
      resumed.registers 8 = descriptionWidth n bound →
      resumed.registers 10 = row.val * rowWidth n bound →
      resumed.registers 12 = fieldLimit →
      resumed.registers 14 = width →
      resumed.registers 16 = rowIndex →
      resumed.registers 17 = caseTag →
      resumed.registers 18 = counter →
      resumed.registers 22 = spine →
      resumed.registers 38 = sixPlusLimit →
      resumed.registers 40 = six →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (9 + (unaryFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
          (row.val * rowWidth n bound) start limit value =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (descriptionWidth n bound)
            (Nat.pair (row.val * rowWidth n bound)
              (Nat.pair start (Nat.pair limit value)))) := rfl
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
  rw [run_pair_instruction (value := Nat.pair limit value)
    (selectiveGrammarCaseProgram_controllerAt (pc := 88) rfl) hpc
    (by rw [hlimit, hvalue]) htailFour]
  rw [show 8 + (unaryFuel + (7 + extraFuel)) =
    (7 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair start (Nat.pair limit value))
    (selectiveGrammarCaseProgram_controllerAt (pc := 89) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) htailThree]
  rw [show 7 + (unaryFuel + (7 + extraFuel)) =
    (6 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair start (Nat.pair limit value)))
    (selectiveGrammarCaseProgram_controllerAt (pc := 90) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htailTwo]
  rw [show 6 + (unaryFuel + (7 + extraFuel)) =
    (5 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair start (Nat.pair limit value))))
    (selectiveGrammarCaseProgram_controllerAt (pc := 91) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) htailOne]
  rw [show 5 + (unaryFuel + (7 + extraFuel)) =
    (4 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveGrammarCaseProgram_controllerAt (pc := 92) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [show 4 + (unaryFuel + (7 + extraFuel)) =
    (3 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveGrammarCaseProgram_controllerAt (pc := 93) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 3 + (unaryFuel + (7 + extraFuel)) =
    (2 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
        (row.val * rowWidth n bound) start limit value)
    (selectiveGrammarCaseProgram_controllerAt (pc := 94) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [show 2 + (unaryFuel + (7 + extraFuel)) =
    (1 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 95) rfl) rfl hzeroBits]
  rw [show 1 + (unaryFuel + (7 + extraFuel)) =
    (unaryFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 96) rfl) rfl]
  simp only [ite_self]
  rw [hunaryFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveUnaryProgram)
    (calleeOutput := selectiveWireCode (selectiveCompileExpr state (unaryEqualsExpr (n := n) row
      start limit value hblock)))
    selectiveGrammarCaseProgram_unaryCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveUnaryProgram_eq_unaryEquals state row start limit value
        hblock hordered frame hframePc ?_)
      hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _unaryHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode (selectiveCompileExpr state
      (unaryEqualsExpr (n := n) row start limit value hblock)))
      (selectiveGrammarCaseProgram_controllerAt (pc := 97) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := selectiveStateCode ((selectiveCompileExpr state
      (unaryEqualsExpr (n := n) row start limit value hblock))).state)
      (selectiveGrammarCaseProgram_controllerAt (pc := 98) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := ((selectiveCompileExpr state (unaryEqualsExpr (n :=
      n) row start limit value hblock))).output)
      (selectiveGrammarCaseProgram_controllerAt (pc := 99) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := (((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit value
        hblock))).state).target - (((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start
        limit value hblock))).state).next)
      (selectiveGrammarCaseProgram_controllerAt (pc := 100) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit value
          hblock))).state).next
          (selectiveSelectedCode (((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start
            limit value hblock))).state).selected))
      (selectiveGrammarCaseProgram_controllerAt (pc := 101) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (((selectiveCompileExpr state (unaryEqualsExpr (n :=
      n) row start limit value hblock))).state).next)
      (selectiveGrammarCaseProgram_controllerAt (pc := 102) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (((selectiveCompileExpr state (unaryEqualsExpr (n := n) row
        start limit value hblock))).state).selected)
      (selectiveGrammarCaseProgram_controllerAt (pc := 103) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hfieldLimit, hwidth, hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix]

private theorem run_selectiveGrammarCaseAddressCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit addressWidth addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (maximumBits addressFuel extraFuel finalOutput : ℕ)
    (fieldLimit width rowIndex caseTag counter spine sixPlusLimit six : ℕ)
    (machine : NPOracleState)
    (haddressFuel :
      addressFuel =
        selectiveAddressSelectRunFuel row start limit addressCode hblock state
          addressWidth)
    (hcalleeBits :
      selectiveAddressSelectRunBits row start limit addressCode hblock state
          addressWidth ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveAddressSelectInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
            addressWidth addressCode) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode (selectiveCompileExpr state (BoolExpr.any
        (selectiveAddressSelectExprs row start limit addressCode hblock 0 addressWidth))))) ≤
        maximumBits)
    (hpc : machine.pc = 78)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth n bound)
    (hrowBase : machine.registers 10 = row.val * rowWidth n bound)
    (hstart : machine.registers 35 = start)
    (hlimit : machine.registers 36 = limit)
    (haddressWidth : machine.registers 32 = addressWidth)
    (haddressCode : machine.registers 34 = addressCode)
    (hfieldLimit : machine.registers 12 = fieldLimit)
    (hwidth : machine.registers 14 = width)
    (hrowIndex : machine.registers 16 = rowIndex)
    (hcaseTag : machine.registers 17 = caseTag)
    (hcounter : machine.registers 18 = counter)
    (hspine : machine.registers 22 = spine)
    (hsixPlusLimit : machine.registers 38 = sixPlusLimit)
    (hsix : machine.registers 40 = six)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 104 →
      resumed.registers 4 = ((selectiveCompileExpr state (BoolExpr.any (selectiveAddressSelectExprs
        row start limit addressCode hblock 0 addressWidth)))).state.target - ((selectiveCompileExpr
        state (BoolExpr.any (selectiveAddressSelectExprs row start limit addressCode hblock 0
        addressWidth)))).state.next →
      resumed.registers 6 = ((selectiveCompileExpr state (BoolExpr.any (selectiveAddressSelectExprs
        row start limit addressCode hblock 0 addressWidth)))).state.next →
      resumed.registers 7 = selectiveSelectedCode ((selectiveCompileExpr state (BoolExpr.any
        (selectiveAddressSelectExprs row start limit addressCode hblock 0
        addressWidth)))).state.selected →
      resumed.registers 20 = ((selectiveCompileExpr state (BoolExpr.any
        (selectiveAddressSelectExprs row start limit addressCode hblock 0 addressWidth)))).output →
      resumed.registers 8 = descriptionWidth n bound →
      resumed.registers 10 = row.val * rowWidth n bound →
      resumed.registers 12 = fieldLimit →
      resumed.registers 14 = width →
      resumed.registers 16 = rowIndex →
      resumed.registers 17 = caseTag →
      resumed.registers 18 = counter →
      resumed.registers 22 = spine →
      resumed.registers 38 = sixPlusLimit →
      resumed.registers 40 = six →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (10 + (addressFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveAddressSelectInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
          addressWidth addressCode =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (descriptionWidth n bound)
            (Nat.pair (row.val * rowWidth n bound)
              (Nat.pair start
                (Nat.pair limit
                  (Nat.pair addressWidth addressCode))))) := rfl
  have hrequestFlat := hrequestBits
  rw [hrequestForm] at hrequestFlat
  have hstateBits := natBitLength_pair_left hrequestFlat
  have htailOne := natBitLength_pair_right hrequestFlat
  have htailTwo := natBitLength_pair_right htailOne
  have htailThree := natBitLength_pair_right htailTwo
  have htailFour := natBitLength_pair_right htailThree
  have htailFive := natBitLength_pair_right htailFour
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
  rw [show 10 + (addressFuel + (7 + extraFuel)) =
    (9 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair addressWidth addressCode)
    (selectiveGrammarCaseProgram_controllerAt (pc := 78) rfl) hpc
    (by rw [haddressWidth, haddressCode]) htailFive]
  rw [show 9 + (addressFuel + (7 + extraFuel)) =
    (8 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair limit (Nat.pair addressWidth addressCode))
    (selectiveGrammarCaseProgram_controllerAt (pc := 79) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit]) htailFour]
  rw [show 8 + (addressFuel + (7 + extraFuel)) =
    (7 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair start (Nat.pair limit (Nat.pair addressWidth addressCode)))
    (selectiveGrammarCaseProgram_controllerAt (pc := 80) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) htailThree]
  rw [show 7 + (addressFuel + (7 + extraFuel)) =
    (6 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair start
          (Nat.pair limit (Nat.pair addressWidth addressCode))))
    (selectiveGrammarCaseProgram_controllerAt (pc := 81) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htailTwo]
  rw [show 6 + (addressFuel + (7 + extraFuel)) =
    (5 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair start
            (Nat.pair limit (Nat.pair addressWidth addressCode)))))
    (selectiveGrammarCaseProgram_controllerAt (pc := 82) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) htailOne]
  rw [show 5 + (addressFuel + (7 + extraFuel)) =
    (4 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveGrammarCaseProgram_controllerAt (pc := 83) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [show 4 + (addressFuel + (7 + extraFuel)) =
    (3 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveGrammarCaseProgram_controllerAt (pc := 84) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 3 + (addressFuel + (7 + extraFuel)) =
    (2 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveAddressSelectInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
        addressWidth addressCode)
    (selectiveGrammarCaseProgram_controllerAt (pc := 85) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [show 2 + (addressFuel + (7 + extraFuel)) =
    (1 + (addressFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 86) rfl) rfl hzeroBits]
  rw [show 1 + (addressFuel + (7 + extraFuel)) =
    (addressFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 87) rfl) rfl]
  simp only [ite_self]
  rw [haddressFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveAddressSelectProgram)
    (calleeOutput := selectiveWireCode (selectiveCompileExpr state (BoolExpr.any
      (selectiveAddressSelectExprs row start limit addressCode hblock 0 addressWidth))))
    selectiveGrammarCaseProgram_addressCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveAddressSelectProgram state row start limit addressWidth
        addressCode hblock hordered frame hframePc ?_)
      hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _addressHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := selectiveWireCode (selectiveCompileExpr state
      (BoolExpr.any (selectiveAddressSelectExprs row start limit addressCode hblock 0
      addressWidth))))
      (selectiveGrammarCaseProgram_controllerAt (pc := 97) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := selectiveStateCode ((selectiveCompileExpr state
      (BoolExpr.any (selectiveAddressSelectExprs row start limit addressCode hblock 0
      addressWidth)))).state)
      (selectiveGrammarCaseProgram_controllerAt (pc := 98) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := ((selectiveCompileExpr state (BoolExpr.any
      (selectiveAddressSelectExprs row start limit addressCode hblock 0 addressWidth)))).output)
      (selectiveGrammarCaseProgram_controllerAt (pc := 99) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := (((selectiveCompileExpr state (BoolExpr.any (selectiveAddressSelectExprs row start
        limit addressCode hblock 0 addressWidth)))).state).target - (((selectiveCompileExpr state
        (BoolExpr.any (selectiveAddressSelectExprs row start limit addressCode hblock 0
        addressWidth)))).state).next)
      (selectiveGrammarCaseProgram_controllerAt (pc := 100) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (((selectiveCompileExpr state (BoolExpr.any (selectiveAddressSelectExprs row start
          limit addressCode hblock 0 addressWidth)))).state).next
          (selectiveSelectedCode (((selectiveCompileExpr state (BoolExpr.any
            (selectiveAddressSelectExprs row start limit addressCode hblock 0
            addressWidth)))).state).selected))
      (selectiveGrammarCaseProgram_controllerAt (pc := 101) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (((selectiveCompileExpr state (BoolExpr.any
      (selectiveAddressSelectExprs row start limit addressCode hblock 0
      addressWidth)))).state).next)
      (selectiveGrammarCaseProgram_controllerAt (pc := 102) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (((selectiveCompileExpr state (BoolExpr.any
        (selectiveAddressSelectExprs row start limit addressCode hblock 0
        addressWidth)))).state).selected)
      (selectiveGrammarCaseProgram_controllerAt (pc := 103) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hfieldLimit, hwidth, hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix]

/-! ## 4. The level premise

§1's scheduling identity and §3's three call frames are exactly the facts the
forward dispatcher (`20`–`77`) and the reverse `and` fold (`109`–`135`) consume,
and §2 decodes every position they touch.  The premise is stated in the runner
shape so the node-row scheduler one level up can consume it unchanged; §9
discharges it. -/

/-- **Level premise.**  The grammar-case compiler compiles one of the seven
grammar row cases at its own ABI frame, at an arbitrary entry state, with
resources depending on the request alone. -/
structure SelectiveGrammarCaseRunner (width bound : ℕ) where
  bits : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    ℕ → ℕ
  fuel : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    ℕ → ℕ
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (row : Fin (bound + 1)) (caseTag : ℕ), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveGrammarCaseInput (selectiveStateCode state)
        (descriptionWidth width bound) (row.val * rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width row.val caseTag →
    runNPOracleProgram selectiveGrammarCaseProgram (bits state row caseTag)
        (fuel state row caseTag) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := width) row row.val caseTag)))

/-! ## 5. The all-ones address word

Four of the seven cases request a bounded field test whose address word is the
all-ones word of some width.  The controller builds that word in place with the
doubling loop at `73`–`77`.  §5 executes that loop and identifies the disjunct
schedule it hands the address selector with the source compiler's own bounded
field test. -/

private theorem jump_registers_eq (machine : NPOracleState)
    (target index : ℕ) :
    (machine.jump target).registers index = machine.registers index := rfl

private theorem write_registers_eq (machine : NPOracleState)
    (register value index : ℕ) (hindex : index ≠ register) :
    (machine.write register value).registers index =
      machine.registers index := by
  simp [NPOracleState.write, hindex]

/-- Interpreter fuel of the doubling loop at `73`–`77`. -/
private def grammarOnesLoopFuel : ℕ → ℕ
  | 0 => 1
  | counter + 1 => 5 + grammarOnesLoopFuel counter

private theorem grammarOnes_le (counter accumulated : ℕ) :
    accumulated ≤ 2 ^ counter * (accumulated + 1) - 1 := by
  have hpow : 1 ≤ 2 ^ counter := Nat.one_le_two_pow
  have : accumulated + 1 ≤ 2 ^ counter * (accumulated + 1) :=
    Nat.le_mul_of_pos_left _ hpow
  omega

-- The doubling loop: one induction on the countdown in `33`.
private theorem run_grammarCaseOnesLoop (maximumBits : ℕ) :
    ∀ (counter accumulated extraFuel finalOutput : ℕ)
      (machine : NPOracleState),
      natBitLength counter ≤ maximumBits →
      natBitLength (2 ^ counter * (accumulated + 1) - 1) ≤ maximumBits →
      machine.pc = 73 →
      machine.registers 33 = counter →
      machine.registers 34 = accumulated →
      (∀ resumed : NPOracleState, resumed.pc = 78 →
        resumed.registers 34 = 2 ^ counter * (accumulated + 1) - 1 →
        (∀ index : ℕ, index ≠ 33 → index ≠ 34 →
          resumed.registers index = machine.registers index) →
        runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
            resumed =
          some finalOutput) →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits
          (grammarOnesLoopFuel counter + extraFuel) machine =
        some finalOutput := by
  intro counter
  induction counter with
  | zero =>
      intro accumulated extraFuel finalOutput machine _ _ hpc hcounter
        haccumulated hcontinue
      rw [show grammarOnesLoopFuel 0 + extraFuel = extraFuel + 1 by
        simp only [grammarOnesLoopFuel]; omega]
      rw [run_branchZero_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 73) rfl) hpc]
      rw [if_pos hcounter]
      refine hcontinue _ rfl ?_ ?_
      · rw [jump_registers_eq, haccumulated]
        simp
      · intro index _ _
        rw [jump_registers_eq]
  | succ counter ih =>
      intro accumulated extraFuel finalOutput machine hcounterBits hfinalBits
        hpc hcounter haccumulated hcontinue
      have hrecEq :
          2 ^ counter * (2 * accumulated + 1 + 1) - 1 =
            2 ^ (counter + 1) * (accumulated + 1) - 1 := by
        rw [Nat.pow_succ]
        ring_nf
      have hstepBits :
          natBitLength (2 * accumulated + 1) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hfinalBits
        have hstep := grammarOnes_le counter (2 * accumulated + 1)
        rw [hrecEq] at hstep
        omega
      have hdoubleBits : natBitLength (2 * accumulated) ≤ maximumBits :=
        (natBitLength_mono (by omega)).trans hstepBits
      have hdownBits : natBitLength counter ≤ maximumBits :=
        (natBitLength_mono (by omega)).trans hcounterBits
      rw [show grammarOnesLoopFuel (counter + 1) + extraFuel =
        (((((grammarOnesLoopFuel counter + extraFuel) + 1) + 1) + 1) + 1) + 1 by
        simp only [grammarOnesLoopFuel]; omega]
      rw [run_branchZero_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 73) rfl) hpc]
      rw [if_neg (by rw [hcounter]; omega)]
      rw [run_add_instruction (value := 2 * accumulated)
        (selectiveGrammarCaseProgram_controllerAt (pc := 74) rfl) rfl
        (by rw [jump_registers_eq, haccumulated]; omega) hdoubleBits]
      rw [run_increment_instruction (value := 2 * accumulated + 1)
        (selectiveGrammarCaseProgram_controllerAt (pc := 75) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hstepBits]
      rw [run_decrement_instruction (value := counter)
        (selectiveGrammarCaseProgram_controllerAt (pc := 76) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hcounter]) hdownBits]
      rw [run_branchZero_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 77) rfl) rfl]
      simp only [ite_self]
      refine ih (2 * accumulated + 1) extraFuel finalOutput _ hdownBits ?_ rfl
        ?_ ?_ ?_
      · rw [hrecEq]; exact hfinalBits
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedOnes hresumedPreserved
        refine hcontinue resumed hresumedPc (by rw [hresumedOnes, hrecEq]) ?_
        intro index hthirtyThree hthirtyFour
        rw [hresumedPreserved index hthirtyThree hthirtyFour]
        simp [NPOracleState.write, NPOracleState.jump, hthirtyThree,
          hthirtyFour]

/-- The disjunct schedule the all-ones word produces is the source compiler's
bounded field test at the same block. -/
private theorem grammarOnesExprs_eq {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit upper : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    ∀ (remaining offset : ℕ), offset + remaining ≤ upper →
      selectiveAddressSelectExprs (n := n) row start limit (2 ^ upper - 1)
          hblock offset remaining =
        (List.range' offset remaining).map fun value =>
          unaryEqualsExpr (n := n) row start limit value hblock := by
  intro remaining
  induction remaining with
  | zero => intro offset _; rfl
  | succ remaining ih =>
      intro offset hoffset
      rw [selectiveAddressSelectExprs, List.range'_succ, List.map_cons,
        ih (offset + 1) (by omega)]
      refine congrArg₂ List.cons ?_ rfl
      simp only [selectiveAddressSelectExpr, Nat.testBit_two_pow_sub_one,
        decide_eq_true_eq]
      rw [if_pos (by omega)]

private theorem grammarFirstFieldLess_eq {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ)
    (hblock : 6 + boundedCircuitFieldLimit n bound ≤ rowWidth n bound) :
    BoolExpr.any
        (selectiveAddressSelectExprs (n := n) row 6
          (boundedCircuitFieldLimit n bound) (2 ^ upper - 1) hblock 0 upper) =
      firstFieldLessExpr (n := n) row upper := by
  rw [grammarOnesExprs_eq row 6 (boundedCircuitFieldLimit n bound) upper hblock
    upper 0 (by omega)]
  rw [firstFieldLessExpr, List.range_eq_range']
  rfl

private theorem grammarSecondFieldLess_eq {n bound : ℕ}
    (row : Fin (bound + 1)) (upper : ℕ)
    (hblock :
      6 + boundedCircuitFieldLimit n bound + boundedCircuitFieldLimit n bound ≤
        rowWidth n bound) :
    BoolExpr.any
        (selectiveAddressSelectExprs (n := n) row
          (6 + boundedCircuitFieldLimit n bound)
          (boundedCircuitFieldLimit n bound) (2 ^ upper - 1) hblock 0 upper) =
      secondFieldLessExpr (n := n) row upper := by
  rw [grammarOnesExprs_eq row (6 + boundedCircuitFieldLimit n bound)
    (boundedCircuitFieldLimit n bound) upper hblock upper 0 (by omega)]
  rw [secondFieldLessExpr, List.range_eq_range']
  rfl

/-! ## 6. The seven-way forward dispatcher

The forward pass visits §1's three conjuncts in order.  The first is always the
row's tag test; the dispatcher at `30`–`52` picks the middle conjunct and the
one at `53`–`70` the last, from the case tag alone.  Every phase ends at the
shared return point `104`, so the live registers below are exactly the frame
each phase both consumes and restores. -/

/-- The controller's live register frame at the loop head and at every return
point: the compiler state, the request constants, the phase counter and the
retained spine. -/
private def GrammarCaseFrame {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag counter spine : ℕ) (machine : NPOracleState) : Prop :=
  machine.registers 4 = state.target - state.next ∧
    machine.registers 6 = state.next ∧
      machine.registers 7 = selectiveSelectedCode state.selected ∧
        machine.registers 8 = descriptionWidth n bound ∧
          machine.registers 10 = row.val * rowWidth n bound ∧
            machine.registers 12 = boundedCircuitFieldLimit n bound ∧
              machine.registers 14 = n ∧
                machine.registers 16 = row.val ∧
                  machine.registers 17 = caseTag ∧
                    machine.registers 18 = counter ∧
                      machine.registers 22 = spine ∧
                        machine.registers 38 =
                            6 + boundedCircuitFieldLimit n bound ∧
                          machine.registers 40 = 6

private theorem grammarTagBlock (n bound : ℕ) :
    (0 : ℕ) + 6 ≤ rowWidth n bound := by
  have hrow : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound := rfl
  omega

private theorem grammarFirstBlock (n bound : ℕ) :
    6 + boundedCircuitFieldLimit n bound ≤ rowWidth n bound := by
  have hrow : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound := rfl
  omega

private theorem grammarSecondBlock (n bound : ℕ) :
    6 + boundedCircuitFieldLimit n bound + boundedCircuitFieldLimit n bound ≤
      rowWidth n bound := by
  have hrow : rowWidth n bound = 6 + 2 * boundedCircuitFieldLimit n bound := rfl
  omega

/-- Register width of one relocated unary-equality block. -/
private def grammarUnaryBlockBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (start limit value : ℕ) (hblock : start + limit ≤ rowWidth n bound) : ℕ :=
  max
    (natBitLength
      (selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
        (row.val * rowWidth n bound) start limit value)) <|
    max
      (selectiveUnaryRunBits state
        (selectiveUnaryEqualsLiterals (n := n) row start limit value hblock)
        (row.val * rowWidth n bound) start value) <|
      natBitLength
        (Nat.pair 0
          (selectiveWireCode
            (selectiveCompileExpr state
              (unaryEqualsExpr (n := n) row start limit value hblock))))

/-- Register width of one relocated address-selection block. -/
private def grammarAddressBlockBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (start limit addressWidth addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) : ℕ :=
  max
    (natBitLength
      (selectiveAddressSelectInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
        addressWidth addressCode)) <|
    max
      (selectiveAddressSelectRunBits row start limit addressCode hblock state
        addressWidth) <|
      natBitLength
        (Nat.pair 0
          (selectiveWireCode
            (selectiveCompileExpr state
              (BoolExpr.any
                (selectiveAddressSelectExprs row start limit addressCode hblock
                  0 addressWidth)))))

/-- Register width of the doubling loop that builds one all-ones word. -/
private def grammarOnesBits (upper : ℕ) : ℕ :=
  max (natBitLength upper) (natBitLength (2 ^ upper - 1))

/-- Interpreter fuel of the tag-test phase. -/
private def grammarPhaseZeroFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag extraFuel : ℕ) : ℕ :=
  6 +
    (9 +
      (selectiveUnaryRunFuel state
          (selectiveUnaryEqualsLiterals (n := n) row 0 6 caseTag
            (grammarTagBlock n bound)) +
        (7 + extraFuel)))

/-- Register width of the tag-test phase. -/
private def grammarPhaseZeroBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : ℕ :=
  grammarUnaryBlockBits state row 0 6 caseTag (grammarTagBlock n bound)

set_option maxHeartbeats 1600000 in
-- Six dispatch steps into the relocated unary compiler at `88`.
private theorem run_grammarCasePhaseZero {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits extraFuel finalOutput spine : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hbits : grammarPhaseZeroBits state row caseTag ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hframe : GrammarCaseFrame state row caseTag 0 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 104 →
      resumed.registers 20 =
        (selectiveCompileExpr state
          (tagEqualsExpr (n := n) row caseTag)).output →
      GrammarCaseFrame
        (selectiveCompileExpr state (tagEqualsExpr (n := n) row caseTag)).state
        row caseTag 0 spine resumed →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (grammarPhaseZeroFuel state row caseTag extraFuel) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix⟩ := hframe
  simp only [grammarPhaseZeroBits, grammarUnaryBlockBits] at hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbits
  have htailOne := (Nat.le_max_right _ _).trans hbits
  have hcalleeBits := (Nat.le_max_left _ _).trans htailOne
  have hwireBits := (Nat.le_max_right _ _).trans htailOne
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hrequestForm :
      selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
          (row.val * rowWidth n bound) 0 6 caseTag =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (descriptionWidth n bound)
            (Nat.pair (row.val * rowWidth n bound)
              (Nat.pair 0 (Nat.pair 6 caseTag)))) := rfl
  have hflat := hrequestBits
  rw [hrequestForm] at hflat
  have hcaseTagBits :=
    natBitLength_pair_right
      (natBitLength_pair_right
        (natBitLength_pair_right
          (natBitLength_pair_right (natBitLength_pair_right hflat))))
  simp only [grammarPhaseZeroFuel]
  rw [show (6 : ℕ) +
      (9 +
        (selectiveUnaryRunFuel state
            (selectiveUnaryEqualsLiterals (n := n) row 0 6 caseTag
              (grammarTagBlock n bound)) +
          (7 + extraFuel))) =
    (9 +
      (selectiveUnaryRunFuel state
          (selectiveUnaryEqualsLiterals (n := n) row 0 6 caseTag
            (grammarTagBlock n bound)) +
        (7 + extraFuel))) + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_copy_instruction (value := 0)
    (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
    (by rw [hcounter]) (hsmall 0 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 26) rfl) rfl
    (hsmall 0 (by omega))]
  rw [run_copy_instruction (value := 6)
    (selectiveGrammarCaseProgram_controllerAt (pc := 27) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hsix])
    (hsmall 6 (by omega))]
  rw [run_copy_instruction (value := caseTag)
    (selectiveGrammarCaseProgram_controllerAt (pc := 28) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag]) hcaseTagBits]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 29) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveGrammarCaseUnaryCall state row 0 6 caseTag
    (grammarTagBlock n bound) hordered maximumBits _ extraFuel finalOutput
    (boundedCircuitFieldLimit n bound) n row.val caseTag 0 spine
    (6 + boundedCircuitFieldLimit n bound) 6 _ rfl hcalleeBits hrequestBits
    hwireBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
  · simp [NPOracleState.write, NPOracleState.jump, hwidth]
  · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
  · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
  · simp [NPOracleState.write, NPOracleState.jump, hcounter]
  · simp [NPOracleState.write, NPOracleState.jump, hspine]
  · simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
  · simp [NPOracleState.write, NPOracleState.jump, hsix]
  · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
      hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
      hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
      hresumedSpine hresumedSixPlus hresumedSix
    exact hcontinue resumed hresumedPc hresumedOutput
      ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
        hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
        hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
        hresumedSix⟩

/-- Interpreter fuel of the middle-conjunct phase. -/
private def grammarPhaseOneFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag extraFuel : ℕ) : ℕ :=
  if caseTag = 0 then
    11 +
      (10 +
        (selectiveAddressSelectRunFuel row 6 (boundedCircuitFieldLimit n bound)
            (2 ^ 2 - 1) (grammarFirstBlock n bound) state 2 +
          (7 + extraFuel)))
  else if caseTag = 1 then
    14 +
      (grammarOnesLoopFuel n +
        (10 +
          (selectiveAddressSelectRunFuel row 6
              (boundedCircuitFieldLimit n bound) (2 ^ n - 1)
              (grammarFirstBlock n bound) state n +
            (7 + extraFuel))))
  else if 6 ≤ caseTag then
    14 +
      (9 +
        (selectiveUnaryRunFuel state
            (selectiveUnaryEqualsLiterals (n := n) row 6
              (boundedCircuitFieldLimit n bound) 0
              (grammarFirstBlock n bound)) +
          (7 + extraFuel)))
  else
    16 +
      (grammarOnesLoopFuel row.val +
        (10 +
          (selectiveAddressSelectRunFuel row 6
              (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
              (grammarFirstBlock n bound) state row.val +
            (7 + extraFuel))))

/-- Register width of the middle-conjunct phase. -/
private def grammarPhaseOneBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : ℕ :=
  max (natBitLength caseTag) <|
    max (natBitLength (boundedCircuitFieldLimit n bound)) <|
      if caseTag = 0 then
        grammarAddressBlockBits state row 6 (boundedCircuitFieldLimit n bound) 2
          (2 ^ 2 - 1) (grammarFirstBlock n bound)
      else if caseTag = 1 then
        max (grammarOnesBits n)
          (grammarAddressBlockBits state row 6
            (boundedCircuitFieldLimit n bound) n (2 ^ n - 1)
            (grammarFirstBlock n bound))
      else if 6 ≤ caseTag then
        grammarUnaryBlockBits state row 6 (boundedCircuitFieldLimit n bound) 0
          (grammarFirstBlock n bound)
      else
        max (grammarOnesBits row.val)
          (grammarAddressBlockBits state row 6
            (boundedCircuitFieldLimit n bound) row.val (2 ^ row.val - 1)
            (grammarFirstBlock n bound))

private theorem grammarOnesAccumulator (upper : ℕ) :
    2 ^ upper * (0 + 1) - 1 = 2 ^ upper - 1 := by
  simp

set_option maxHeartbeats 3200000 in
-- The four-way middle dispatcher at `30`–`52`, into whichever callee the case
-- tag selects.
private theorem run_grammarCasePhaseOne {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits extraFuel finalOutput spine : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hbits : grammarPhaseOneBits state row caseTag ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hframe : GrammarCaseFrame state row caseTag 1 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 104 →
      resumed.registers 20 =
        (selectiveCompileExpr state
          (selectiveGrammarCaseFirstField (n := n) row row.val caseTag)).output →
      GrammarCaseFrame
        (selectiveCompileExpr state
          (selectiveGrammarCaseFirstField (n := n) row row.val caseTag)).state
        row caseTag 1 spine resumed →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (grammarPhaseOneFuel state row caseTag extraFuel) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix⟩ := hframe
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  unfold grammarPhaseOneFuel
  unfold grammarPhaseOneBits at hbits
  have hcaseTagBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hfieldLimitBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  by_cases hzero : caseTag = 0
  · rw [if_pos hzero]
    rw [if_pos hzero] at hbitsTwo
    unfold grammarAddressBlockBits at hbitsTwo
    have hrequestBits := (Nat.le_max_left _ _).trans hbitsTwo
    have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
    have hcalleeBits := (Nat.le_max_left _ _).trans hbitsThree
    have hwireBits := (Nat.le_max_right _ _).trans hbitsThree
    have hexpr :
        selectiveGrammarCaseFirstField (n := n) row row.val caseTag =
          BoolExpr.any
            (selectiveAddressSelectExprs (n := n) row 6
              (boundedCircuitFieldLimit n bound) (2 ^ 2 - 1)
              (grammarFirstBlock n bound) 0 2) := by
      rw [grammarFirstFieldLess_eq]
      simp [selectiveGrammarCaseFirstField, hzero]
    rw [hexpr] at hcontinue
    rw [show (11 : ℕ) +
        (10 +
          (selectiveAddressSelectRunFuel row 6
              (boundedCircuitFieldLimit n bound) (2 ^ 2 - 1)
              (grammarFirstBlock n bound) state 2 +
            (7 + extraFuel))) =
      (10 +
        (selectiveAddressSelectRunFuel row 6 (boundedCircuitFieldLimit n bound)
            (2 ^ 2 - 1) (grammarFirstBlock n bound) state 2 +
          (7 + extraFuel))) +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_copy_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
      (by rw [hcounter]) (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 22) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 23) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_copy_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag, hzero])
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 31) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_copy_instruction (value := 6)
      (selectiveGrammarCaseProgram_controllerAt (pc := 36) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hsix])
      (hsmall 6 (by omega))]
    rw [run_copy_instruction (value := boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 37) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit])
      hfieldLimitBits]
    rw [run_set_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 38) rfl) rfl
      (hsmall 2 (by omega))]
    rw [run_set_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 39) rfl) rfl
      (hsmall 3 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 40) rfl) rfl]
    simp only [ite_self]
    refine run_selectiveGrammarCaseAddressCall state row 6
      (boundedCircuitFieldLimit n bound) 2 (2 ^ 2 - 1)
      (grammarFirstBlock n bound) hordered maximumBits _ extraFuel finalOutput
      (boundedCircuitFieldLimit n bound) n row.val caseTag 1 spine
      (6 + boundedCircuitFieldLimit n bound) 6 _ rfl hcalleeBits hrequestBits
      hwireBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump, hremaining]
    · simp [NPOracleState.write, NPOracleState.jump, hnext]
    · simp [NPOracleState.write, NPOracleState.jump, hselected]
    · simp [NPOracleState.write, NPOracleState.jump, harity]
    · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump, hwidth]
    · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
    · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
    · simp [NPOracleState.write, NPOracleState.jump, hcounter]
    · simp [NPOracleState.write, NPOracleState.jump, hspine]
    · simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
    · simp [NPOracleState.write, NPOracleState.jump, hsix]
    · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
        hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
        hresumedSpine hresumedSixPlus hresumedSix
      exact hcontinue resumed hresumedPc hresumedOutput
        ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
          hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
          hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
          hresumedSix⟩
  rw [if_neg hzero]
  rw [if_neg hzero] at hbitsTwo
  by_cases hone : caseTag = 1
  · rw [if_pos hone]
    rw [if_pos hone] at hbitsTwo
    have honesBits := (Nat.le_max_left _ _).trans hbitsTwo
    have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
    unfold grammarOnesBits at honesBits
    have hupperBits := (Nat.le_max_left _ _).trans honesBits
    have hcodeBits := (Nat.le_max_right _ _).trans honesBits
    unfold grammarAddressBlockBits at hbitsThree
    have hrequestBits := (Nat.le_max_left _ _).trans hbitsThree
    have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
    have hcalleeBits := (Nat.le_max_left _ _).trans hbitsFour
    have hwireBits := (Nat.le_max_right _ _).trans hbitsFour
    have hexpr :
        selectiveGrammarCaseFirstField (n := n) row row.val caseTag =
          BoolExpr.any
            (selectiveAddressSelectExprs (n := n) row 6
              (boundedCircuitFieldLimit n bound) (2 ^ n - 1)
              (grammarFirstBlock n bound) 0 n) := by
      rw [grammarFirstFieldLess_eq]
      simp [selectiveGrammarCaseFirstField, hone]
    rw [hexpr] at hcontinue
    rw [show (14 : ℕ) +
        (grammarOnesLoopFuel n +
          (10 +
            (selectiveAddressSelectRunFuel row 6
                (boundedCircuitFieldLimit n bound) (2 ^ n - 1)
                (grammarFirstBlock n bound) state n +
              (7 + extraFuel)))) =
      (grammarOnesLoopFuel n +
        (10 +
          (selectiveAddressSelectRunFuel row 6
              (boundedCircuitFieldLimit n bound) (2 ^ n - 1)
              (grammarFirstBlock n bound) state n +
            (7 + extraFuel)))) +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_copy_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
      (by rw [hcounter]) (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 22) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 23) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_copy_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag, hone])
      (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 31) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 32) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 33) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_copy_instruction (value := 6)
      (selectiveGrammarCaseProgram_controllerAt (pc := 41) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hsix])
      (hsmall 6 (by omega))]
    rw [run_copy_instruction (value := boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 42) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit])
      hfieldLimitBits]
    rw [run_copy_instruction (value := n)
      (selectiveGrammarCaseProgram_controllerAt (pc := 43) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hupperBits]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 44) rfl) rfl]
    simp only [ite_self]
    rw [run_copy_instruction (value := n)
      (selectiveGrammarCaseProgram_controllerAt (pc := 71) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hupperBits]
    rw [run_set_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 72) rfl) rfl
      (hsmall 0 (by omega))]
    refine run_grammarCaseOnesLoop maximumBits n 0 _ finalOutput _ hupperBits
      (by rw [grammarOnesAccumulator]; exact hcodeBits) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) ?_
    intro middle hmiddlePc hmiddleCode hmiddlePreserved
    refine run_selectiveGrammarCaseAddressCall state row 6
      (boundedCircuitFieldLimit n bound) n (2 ^ n - 1)
      (grammarFirstBlock n bound) hordered maximumBits _ extraFuel finalOutput
      (boundedCircuitFieldLimit n bound) n row.val caseTag 1 spine
      (6 + boundedCircuitFieldLimit n bound) 6 middle rfl hcalleeBits
      hrequestBits hwireBits hmiddlePc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_
    · rw [hmiddlePreserved 4 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hremaining]
    · rw [hmiddlePreserved 6 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hnext]
    · rw [hmiddlePreserved 7 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hselected]
    · rw [hmiddlePreserved 8 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, harity]
    · rw [hmiddlePreserved 10 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hrowBase]
    · rw [hmiddlePreserved 35 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]
    · rw [hmiddlePreserved 36 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]
    · rw [hmiddlePreserved 32 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]
    · rw [hmiddleCode, grammarOnesAccumulator]
    · rw [hmiddlePreserved 12 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
    · rw [hmiddlePreserved 14 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hwidth]
    · rw [hmiddlePreserved 16 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
    · rw [hmiddlePreserved 17 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
    · rw [hmiddlePreserved 18 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hcounter]
    · rw [hmiddlePreserved 22 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hspine]
    · rw [hmiddlePreserved 38 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
    · rw [hmiddlePreserved 40 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump, hsix]
    · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
        hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
        hresumedSpine hresumedSixPlus hresumedSix
      exact hcontinue resumed hresumedPc hresumedOutput
        ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
          hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
          hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
          hresumedSix⟩
  rw [if_neg hone]
  rw [if_neg hone] at hbitsTwo
  by_cases hbig : 6 ≤ caseTag
  · rw [if_pos hbig]
    rw [if_pos hbig] at hbitsTwo
    unfold grammarUnaryBlockBits at hbitsTwo
    have hrequestBits := (Nat.le_max_left _ _).trans hbitsTwo
    have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
    have hcalleeBits := (Nat.le_max_left _ _).trans hbitsThree
    have hwireBits := (Nat.le_max_right _ _).trans hbitsThree
    have hexpr :
        selectiveGrammarCaseFirstField (n := n) row row.val caseTag =
          unaryEqualsExpr (n := n) row 6 (boundedCircuitFieldLimit n bound) 0
            (grammarFirstBlock n bound) := by
      simp only [selectiveGrammarCaseFirstField, if_neg hzero, if_neg hone,
        if_pos hbig]
      rfl
    rw [hexpr] at hcontinue
    rw [show (14 : ℕ) +
        (9 +
          (selectiveUnaryRunFuel state
              (selectiveUnaryEqualsLiterals (n := n) row 6
                (boundedCircuitFieldLimit n bound) 0
                (grammarFirstBlock n bound)) +
            (7 + extraFuel))) =
      (9 +
        (selectiveUnaryRunFuel state
            (selectiveUnaryEqualsLiterals (n := n) row 6
              (boundedCircuitFieldLimit n bound) 0
              (grammarFirstBlock n bound)) +
          (7 + extraFuel))) +
        1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_copy_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
      (by rw [hcounter]) (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 22) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 23) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_copy_instruction (value := caseTag)
      (selectiveGrammarCaseProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag])
      hcaseTagBits]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 31) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
    rw [run_decrement_instruction (value := caseTag - 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 32) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      ((natBitLength_mono (by omega)).trans hcaseTagBits)]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 33) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
    rw [run_subtract_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 34) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hsix, hcaseTag]; omega)
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 35) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_copy_instruction (value := 6)
      (selectiveGrammarCaseProgram_controllerAt (pc := 45) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hsix])
      (hsmall 6 (by omega))]
    rw [run_copy_instruction (value := boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 46) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit])
      hfieldLimitBits]
    rw [run_set_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 47) rfl) rfl
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 48) rfl) rfl]
    simp only [ite_self]
    refine run_selectiveGrammarCaseUnaryCall state row 6
      (boundedCircuitFieldLimit n bound) 0 (grammarFirstBlock n bound) hordered
      maximumBits _ extraFuel finalOutput (boundedCircuitFieldLimit n bound) n
      row.val caseTag 1 spine (6 + boundedCircuitFieldLimit n bound) 6 _ rfl
      hcalleeBits hrequestBits hwireBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump, hremaining]
    · simp [NPOracleState.write, NPOracleState.jump, hnext]
    · simp [NPOracleState.write, NPOracleState.jump, hselected]
    · simp [NPOracleState.write, NPOracleState.jump, harity]
    · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump, hwidth]
    · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
    · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
    · simp [NPOracleState.write, NPOracleState.jump, hcounter]
    · simp [NPOracleState.write, NPOracleState.jump, hspine]
    · simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
    · simp [NPOracleState.write, NPOracleState.jump, hsix]
    · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
        hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
        hresumedSpine hresumedSixPlus hresumedSix
      exact hcontinue resumed hresumedPc hresumedOutput
        ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
          hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
          hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
          hresumedSix⟩
  rw [if_neg hbig]
  rw [if_neg hbig] at hbitsTwo
  have honesBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  unfold grammarOnesBits at honesBits
  have hupperBits := (Nat.le_max_left _ _).trans honesBits
  have hcodeBits := (Nat.le_max_right _ _).trans honesBits
  unfold grammarAddressBlockBits at hbitsThree
  have hrequestBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have hcalleeBits := (Nat.le_max_left _ _).trans hbitsFour
  have hwireBits := (Nat.le_max_right _ _).trans hbitsFour
  have hexpr :
      selectiveGrammarCaseFirstField (n := n) row row.val caseTag =
        BoolExpr.any
          (selectiveAddressSelectExprs (n := n) row 6
            (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
            (grammarFirstBlock n bound) 0 row.val) := by
    rw [grammarFirstFieldLess_eq]
    simp only [selectiveGrammarCaseFirstField, if_neg hzero, if_neg hone,
      if_neg hbig]
  rw [hexpr] at hcontinue
  rw [show (16 : ℕ) +
      (grammarOnesLoopFuel row.val +
        (10 +
          (selectiveAddressSelectRunFuel row 6
              (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
              (grammarFirstBlock n bound) state row.val +
            (7 + extraFuel)))) =
    (grammarOnesLoopFuel row.val +
      (10 +
        (selectiveAddressSelectRunFuel row 6 (boundedCircuitFieldLimit n bound)
            (2 ^ row.val - 1) (grammarFirstBlock n bound) state row.val +
          (7 + extraFuel)))) +
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_copy_instruction (value := 1)
    (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
    (by rw [hcounter]) (hsmall 1 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_decrement_instruction (value := 0)
    (selectiveGrammarCaseProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 0 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 23) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_copy_instruction (value := caseTag)
    (selectiveGrammarCaseProgram_controllerAt (pc := 30) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag]) hcaseTagBits]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 31) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
  rw [run_decrement_instruction (value := caseTag - 1)
    (selectiveGrammarCaseProgram_controllerAt (pc := 32) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (by omega)).trans hcaseTagBits)]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 33) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
  rw [run_subtract_instruction (value := 6 - caseTag)
    (selectiveGrammarCaseProgram_controllerAt (pc := 34) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hsix, hcaseTag])
    (hsmall (6 - caseTag) (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 35) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
  rw [run_copy_instruction (value := 6)
    (selectiveGrammarCaseProgram_controllerAt (pc := 49) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hsix])
    (hsmall 6 (by omega))]
  rw [run_copy_instruction (value := boundedCircuitFieldLimit n bound)
    (selectiveGrammarCaseProgram_controllerAt (pc := 50) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit])
    hfieldLimitBits]
  rw [run_copy_instruction (value := row.val)
    (selectiveGrammarCaseProgram_controllerAt (pc := 51) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowIndex]) hupperBits]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 52) rfl) rfl]
  simp only [ite_self]
  rw [run_copy_instruction (value := row.val)
    (selectiveGrammarCaseProgram_controllerAt (pc := 71) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hupperBits]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 72) rfl) rfl
    (hsmall 0 (by omega))]
  refine run_grammarCaseOnesLoop maximumBits row.val 0 _ finalOutput _
    hupperBits (by rw [grammarOnesAccumulator]; exact hcodeBits) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro middle hmiddlePc hmiddleCode hmiddlePreserved
  refine run_selectiveGrammarCaseAddressCall state row 6
    (boundedCircuitFieldLimit n bound) row.val (2 ^ row.val - 1)
    (grammarFirstBlock n bound) hordered maximumBits _ extraFuel finalOutput
    (boundedCircuitFieldLimit n bound) n row.val caseTag 1 spine
    (6 + boundedCircuitFieldLimit n bound) 6 middle rfl hcalleeBits hrequestBits
    hwireBits hmiddlePc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hmiddlePreserved 4 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · rw [hmiddlePreserved 6 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hnext]
  · rw [hmiddlePreserved 7 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hselected]
  · rw [hmiddlePreserved 8 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, harity]
  · rw [hmiddlePreserved 10 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hrowBase]
  · rw [hmiddlePreserved 35 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  · rw [hmiddlePreserved 36 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  · rw [hmiddlePreserved 32 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump]
  · rw [hmiddleCode, grammarOnesAccumulator]
  · rw [hmiddlePreserved 12 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
  · rw [hmiddlePreserved 14 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hwidth]
  · rw [hmiddlePreserved 16 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
  · rw [hmiddlePreserved 17 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
  · rw [hmiddlePreserved 18 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hcounter]
  · rw [hmiddlePreserved 22 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hspine]
  · rw [hmiddlePreserved 38 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
  · rw [hmiddlePreserved 40 (by omega) (by omega)]
    simp [NPOracleState.write, NPOracleState.jump, hsix]
  · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
      hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
      hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
      hresumedSpine hresumedSixPlus hresumedSix
    exact hcontinue resumed hresumedPc hresumedOutput
      ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
        hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
        hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
        hresumedSix⟩

-- Seven steps from the loop head to the last-conjunct dispatcher at `54`.
private theorem run_grammarCasePhaseTwoPrologue
    (caseTag maximumBits tailFuel finalOutput : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hcaseTagBits : natBitLength caseTag ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hcaseTag : machine.registers 17 = caseTag)
    (hcounter : machine.registers 18 = 2)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 54 →
      resumed.registers 28 = caseTag →
      (∀ index : ℕ, index ≠ 28 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits tailFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (7 + tailFuel) machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  rw [show (7 : ℕ) + tailFuel = tailFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_copy_instruction (value := 2)
    (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
    (by rw [hcounter]) (hsmall 2 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_decrement_instruction (value := 1)
    (selectiveGrammarCaseProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 1 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 23) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_decrement_instruction (value := 0)
    (selectiveGrammarCaseProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 0 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 25) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_copy_instruction (value := caseTag)
    (selectiveGrammarCaseProgram_controllerAt (pc := 53) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag]) hcaseTagBits]
  refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro index hindex
  simp [NPOracleState.write, NPOracleState.jump, hindex]

-- The five case tags whose last field is the constant test reach the shared
-- block at `63`; the two remaining tags reach the bounded block at `67`.
private theorem run_grammarCasePhaseTwoDispatch
    (caseTag maximumBits tailFuel finalOutput : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hcaseTagBits : natBitLength caseTag ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hcaseTag : machine.registers 17 = caseTag)
    (hcounter : machine.registers 18 = 2)
    (hcontinue : ∀ resumed : NPOracleState,
      resumed.pc = (if caseTag = 3 ∨ caseTag = 4 then 67 else 63) →
      (∀ index : ℕ, index ≠ 28 →
        resumed.registers index = machine.registers index) →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits tailFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (16 + tailFuel) machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hdrop : ∀ step : ℕ, natBitLength (caseTag - step) ≤ maximumBits :=
    fun step => (natBitLength_mono (by omega)).trans hcaseTagBits
  rw [show (16 : ℕ) + tailFuel = 7 + (9 + tailFuel) by omega]
  refine run_grammarCasePhaseTwoPrologue caseTag maximumBits _ finalOutput
    machine hsevenBits hcaseTagBits hpc hcaseTag hcounter ?_
  intro middle hmiddlePc hmiddleCase hmiddlePreserved
  have hclose : ∀ (extra : ℕ) (resumed : NPOracleState),
      resumed.pc = (if caseTag = 3 ∨ caseTag = 4 then 67 else 63) →
      (∀ index : ℕ, index ≠ 28 →
        resumed.registers index = middle.registers index) →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits
          (tailFuel + extra) resumed =
        some finalOutput := by
    intro extra resumed hresumedPc hresumedPreserved
    refine run_fuel_add (hcontinue resumed hresumedPc ?_) extra
    intro index hindex
    rw [hresumedPreserved index hindex, hmiddlePreserved index hindex]
  by_cases hzero : caseTag = 0
  · rw [show (9 : ℕ) + tailFuel = (tailFuel + 8) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 54) rfl) hmiddlePc]
    rw [if_pos (by rw [hmiddleCase, hzero])]
    refine hclose 8 _ (by rw [if_neg (by omega)]; rfl) ?_
    intro index _
    rw [jump_registers_eq]
  by_cases hone : caseTag = 1
  · rw [show (9 : ℕ) + tailFuel = (tailFuel + 6) + 1 + 1 + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 54) rfl) hmiddlePc]
    rw [if_neg (by rw [hmiddleCase, hone]; omega)]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [hmiddleCase, hone]) (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 56) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    refine hclose 6 _ (by rw [if_neg (by omega)]; rfl) ?_
    intro index hindex
    simp [NPOracleState.write, NPOracleState.jump, hindex]
  by_cases htwo : caseTag = 2
  · rw [show (9 : ℕ) + tailFuel = (tailFuel + 4) + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 54) rfl) hmiddlePc]
    rw [if_neg (by rw [hmiddleCase, htwo]; omega)]
    rw [run_decrement_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [hmiddleCase, htwo]) (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 56) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 58) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    refine hclose 4 _ (by rw [if_neg (by omega)]; rfl) ?_
    intro index hindex
    simp [NPOracleState.write, NPOracleState.jump, hindex]
  by_cases hthree : caseTag = 3
  · rw [show (9 : ℕ) + tailFuel =
      (tailFuel + 2) + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 54) rfl) hmiddlePc]
    rw [if_neg (by rw [hmiddleCase, hthree]; omega)]
    rw [run_decrement_instruction (value := 2)
      (selectiveGrammarCaseProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [hmiddleCase, hthree]) (hsmall 2 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 56) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 58) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 60) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    refine hclose 2 _ (by rw [if_pos (by omega)]; rfl) ?_
    intro index hindex
    simp [NPOracleState.write, NPOracleState.jump, hindex]
  by_cases hfour : caseTag = 4
  · rw [show (9 : ℕ) + tailFuel =
      tailFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 54) rfl) hmiddlePc]
    rw [if_neg (by rw [hmiddleCase, hfour]; omega)]
    rw [run_decrement_instruction (value := 3)
      (selectiveGrammarCaseProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [hmiddleCase, hfour]) (hsmall 3 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 56) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 2)
      (selectiveGrammarCaseProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 2 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 58) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 1 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 60) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [run_decrement_instruction (value := 0)
      (selectiveGrammarCaseProgram_controllerAt (pc := 61) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 62) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
    refine hclose 0 _ (by rw [if_pos (by omega)]; rfl) ?_
    intro index hindex
    simp [NPOracleState.write, NPOracleState.jump, hindex]
  · rw [show (9 : ℕ) + tailFuel =
      tailFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 54) rfl) hmiddlePc]
    rw [if_neg (by rw [hmiddleCase]; omega)]
    rw [run_decrement_instruction (value := caseTag - 1)
      (selectiveGrammarCaseProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [hmiddleCase]) (hdrop 1)]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 56) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
    rw [run_decrement_instruction (value := caseTag - 2)
      (selectiveGrammarCaseProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]; omega) (hdrop 2)]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 58) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
    rw [run_decrement_instruction (value := caseTag - 3)
      (selectiveGrammarCaseProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]; omega) (hdrop 3)]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 60) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
    rw [run_decrement_instruction (value := caseTag - 4)
      (selectiveGrammarCaseProgram_controllerAt (pc := 61) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]; omega) (hdrop 4)]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 62) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump]; omega)]
    refine hclose 0 _ (by rw [if_neg (by omega)]; rfl) ?_
    intro index hindex
    simp [NPOracleState.write, NPOracleState.jump, hindex]

/-- Interpreter fuel of the last-conjunct phase. -/
private def grammarPhaseTwoFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag extraFuel : ℕ) : ℕ :=
  if caseTag = 3 ∨ caseTag = 4 then
    22 +
      (grammarOnesLoopFuel row.val +
        (10 +
          (selectiveAddressSelectRunFuel row
              (6 + boundedCircuitFieldLimit n bound)
              (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
              (grammarSecondBlock n bound) state row.val +
            (7 + extraFuel))))
  else
    20 +
      (9 +
        (selectiveUnaryRunFuel state
            (selectiveUnaryEqualsLiterals (n := n) row
              (6 + boundedCircuitFieldLimit n bound)
              (boundedCircuitFieldLimit n bound) 0
              (grammarSecondBlock n bound)) +
          (7 + extraFuel)))

/-- Register width of the last-conjunct phase. -/
private def grammarPhaseTwoBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : ℕ :=
  max (natBitLength caseTag) <|
    max (natBitLength (boundedCircuitFieldLimit n bound)) <|
      max (natBitLength (6 + boundedCircuitFieldLimit n bound)) <|
        if caseTag = 3 ∨ caseTag = 4 then
          max (grammarOnesBits row.val)
            (grammarAddressBlockBits state row
              (6 + boundedCircuitFieldLimit n bound)
              (boundedCircuitFieldLimit n bound) row.val (2 ^ row.val - 1)
              (grammarSecondBlock n bound))
        else
          grammarUnaryBlockBits state row (6 + boundedCircuitFieldLimit n bound)
            (boundedCircuitFieldLimit n bound) 0 (grammarSecondBlock n bound)

set_option maxHeartbeats 3200000 in
-- The last-conjunct phase: §6's dispatcher into whichever callee the case tag
-- selects.
private theorem run_grammarCasePhaseTwo {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits extraFuel finalOutput spine : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hbits : grammarPhaseTwoBits state row caseTag ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hframe : GrammarCaseFrame state row caseTag 2 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 104 →
      resumed.registers 20 =
        (selectiveCompileExpr state
          (selectiveGrammarCaseSecondField (n := n) row row.val
            caseTag)).output →
      GrammarCaseFrame
        (selectiveCompileExpr state
          (selectiveGrammarCaseSecondField (n := n) row row.val caseTag)).state
        row caseTag 2 spine resumed →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits
        (grammarPhaseTwoFuel state row caseTag extraFuel) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix⟩ := hframe
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  unfold grammarPhaseTwoFuel
  unfold grammarPhaseTwoBits at hbits
  have hcaseTagBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hfieldLimitBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hsixPlusBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  by_cases hcase : caseTag = 3 ∨ caseTag = 4
  · rw [if_pos hcase]
    rw [if_pos hcase] at hbitsThree
    have honesBits := (Nat.le_max_left _ _).trans hbitsThree
    have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
    unfold grammarOnesBits at honesBits
    have hupperBits := (Nat.le_max_left _ _).trans honesBits
    have hcodeBits := (Nat.le_max_right _ _).trans honesBits
    unfold grammarAddressBlockBits at hbitsFour
    have hrequestBits := (Nat.le_max_left _ _).trans hbitsFour
    have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
    have hcalleeBits := (Nat.le_max_left _ _).trans hbitsFive
    have hwireBits := (Nat.le_max_right _ _).trans hbitsFive
    have hexpr :
        selectiveGrammarCaseSecondField (n := n) row row.val caseTag =
          BoolExpr.any
            (selectiveAddressSelectExprs (n := n) row
              (6 + boundedCircuitFieldLimit n bound)
              (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
              (grammarSecondBlock n bound) 0 row.val) := by
      rw [grammarSecondFieldLess_eq]
      simp only [selectiveGrammarCaseSecondField, if_pos hcase]
    rw [hexpr] at hcontinue
    rw [show (22 : ℕ) +
        (grammarOnesLoopFuel row.val +
          (10 +
            (selectiveAddressSelectRunFuel row
                (6 + boundedCircuitFieldLimit n bound)
                (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
                (grammarSecondBlock n bound) state row.val +
              (7 + extraFuel)))) =
      16 +
        ((grammarOnesLoopFuel row.val +
            (10 +
              (selectiveAddressSelectRunFuel row
                  (6 + boundedCircuitFieldLimit n bound)
                  (boundedCircuitFieldLimit n bound) (2 ^ row.val - 1)
                  (grammarSecondBlock n bound) state row.val +
                (7 + extraFuel)))) + 1 + 1 + 1 + 1 + 1 + 1) by omega]
    refine run_grammarCasePhaseTwoDispatch caseTag maximumBits _ finalOutput
      machine hsevenBits hcaseTagBits hpc hcaseTag hcounter ?_
    intro middle hmiddlePc hmiddlePreserved
    rw [if_pos hcase] at hmiddlePc
    rw [run_copy_instruction (value := 6 + boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 67) rfl) hmiddlePc
      (by rw [hmiddlePreserved 38 (by omega), hsixPlusLimit]) hsixPlusBits]
    rw [run_copy_instruction (value := boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 68) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hmiddlePreserved 12 (by omega), hfieldLimit])
      hfieldLimitBits]
    rw [run_copy_instruction (value := row.val)
      (selectiveGrammarCaseProgram_controllerAt (pc := 69) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hmiddlePreserved 16 (by omega), hrowIndex])
      hupperBits]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 70) rfl) rfl]
    simp only [ite_self]
    rw [run_copy_instruction (value := row.val)
      (selectiveGrammarCaseProgram_controllerAt (pc := 71) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hupperBits]
    rw [run_set_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 72) rfl) rfl
      (hsmall 0 (by omega))]
    refine run_grammarCaseOnesLoop maximumBits row.val 0 _ finalOutput _
      hupperBits (by rw [grammarOnesAccumulator]; exact hcodeBits) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump]) ?_
    intro final hfinalPc hfinalCode hfinalPreserved
    refine run_selectiveGrammarCaseAddressCall state row
      (6 + boundedCircuitFieldLimit n bound)
      (boundedCircuitFieldLimit n bound) row.val (2 ^ row.val - 1)
      (grammarSecondBlock n bound) hordered maximumBits _ extraFuel finalOutput
      (boundedCircuitFieldLimit n bound) n row.val caseTag 2 spine
      (6 + boundedCircuitFieldLimit n bound) 6 final rfl hcalleeBits
      hrequestBits hwireBits hfinalPc ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_
    · rw [hfinalPreserved 4 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 4 (by omega), hremaining]
    · rw [hfinalPreserved 6 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 6 (by omega), hnext]
    · rw [hfinalPreserved 7 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 7 (by omega), hselected]
    · rw [hfinalPreserved 8 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 8 (by omega), harity]
    · rw [hfinalPreserved 10 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 10 (by omega), hrowBase]
    · rw [hfinalPreserved 35 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]
    · rw [hfinalPreserved 36 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]
    · rw [hfinalPreserved 32 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump]
    · rw [hfinalCode, grammarOnesAccumulator]
    · rw [hfinalPreserved 12 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 12 (by omega), hfieldLimit]
    · rw [hfinalPreserved 14 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 14 (by omega), hwidth]
    · rw [hfinalPreserved 16 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 16 (by omega), hrowIndex]
    · rw [hfinalPreserved 17 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 17 (by omega), hcaseTag]
    · rw [hfinalPreserved 18 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 18 (by omega), hcounter]
    · rw [hfinalPreserved 22 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 22 (by omega), hspine]
    · rw [hfinalPreserved 38 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 38 (by omega), hsixPlusLimit]
    · rw [hfinalPreserved 40 (by omega) (by omega)]
      simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 40 (by omega), hsix]
    · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
        hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
        hresumedSpine hresumedSixPlus hresumedSix
      exact hcontinue resumed hresumedPc hresumedOutput
        ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
          hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
          hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
          hresumedSix⟩
  · rw [if_neg hcase]
    rw [if_neg hcase] at hbitsThree
    unfold grammarUnaryBlockBits at hbitsThree
    have hrequestBits := (Nat.le_max_left _ _).trans hbitsThree
    have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
    have hcalleeBits := (Nat.le_max_left _ _).trans hbitsFour
    have hwireBits := (Nat.le_max_right _ _).trans hbitsFour
    have hexpr :
        selectiveGrammarCaseSecondField (n := n) row row.val caseTag =
          unaryEqualsExpr (n := n) row (6 + boundedCircuitFieldLimit n bound)
            (boundedCircuitFieldLimit n bound) 0
            (grammarSecondBlock n bound) := by
      simp only [selectiveGrammarCaseSecondField, if_neg hcase]
      rfl
    rw [hexpr] at hcontinue
    rw [show (20 : ℕ) +
        (9 +
          (selectiveUnaryRunFuel state
              (selectiveUnaryEqualsLiterals (n := n) row
                (6 + boundedCircuitFieldLimit n bound)
                (boundedCircuitFieldLimit n bound) 0
                (grammarSecondBlock n bound)) +
            (7 + extraFuel))) =
      16 +
        ((9 +
            (selectiveUnaryRunFuel state
                (selectiveUnaryEqualsLiterals (n := n) row
                  (6 + boundedCircuitFieldLimit n bound)
                  (boundedCircuitFieldLimit n bound) 0
                  (grammarSecondBlock n bound)) +
              (7 + extraFuel))) + 1 + 1 + 1 + 1) by omega]
    refine run_grammarCasePhaseTwoDispatch caseTag maximumBits _ finalOutput
      machine hsevenBits hcaseTagBits hpc hcaseTag hcounter ?_
    intro middle hmiddlePc hmiddlePreserved
    rw [if_neg hcase] at hmiddlePc
    rw [run_copy_instruction (value := 6 + boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 63) rfl) hmiddlePc
      (by rw [hmiddlePreserved 38 (by omega), hsixPlusLimit]) hsixPlusBits]
    rw [run_copy_instruction (value := boundedCircuitFieldLimit n bound)
      (selectiveGrammarCaseProgram_controllerAt (pc := 64) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hmiddlePreserved 12 (by omega), hfieldLimit])
      hfieldLimitBits]
    rw [run_set_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 65) rfl) rfl
      (hsmall 0 (by omega))]
    rw [run_branchZero_instruction
      (selectiveGrammarCaseProgram_controllerAt (pc := 66) rfl) rfl]
    simp only [ite_self]
    refine run_selectiveGrammarCaseUnaryCall state row
      (6 + boundedCircuitFieldLimit n bound)
      (boundedCircuitFieldLimit n bound) 0 (grammarSecondBlock n bound) hordered
      maximumBits _ extraFuel finalOutput (boundedCircuitFieldLimit n bound) n
      row.val caseTag 2 spine (6 + boundedCircuitFieldLimit n bound) 6 _ rfl
      hcalleeBits hrequestBits hwireBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 4 (by omega), hremaining]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 6 (by omega), hnext]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 7 (by omega), hselected]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 8 (by omega), harity]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 10 (by omega), hrowBase]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 12 (by omega), hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 14 (by omega), hwidth]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 16 (by omega), hrowIndex]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 17 (by omega), hcaseTag]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 18 (by omega), hcounter]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 22 (by omega), hspine]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 38 (by omega), hsixPlusLimit]
    · simp [NPOracleState.write, NPOracleState.jump,
        hmiddlePreserved 40 (by omega), hsix]
    · intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedOutput hresumedArity hresumedRowBase hresumedFieldLimit
        hresumedWidth hresumedRowIndex hresumedCaseTag hresumedCounter
        hresumedSpine hresumedSixPlus hresumedSix
      exact hcontinue resumed hresumedPc hresumedOutput
        ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
          hresumedRowBase, hresumedFieldLimit, hresumedWidth, hresumedRowIndex,
          hresumedCaseTag, hresumedCounter, hresumedSpine, hresumedSixPlus,
          hresumedSix⟩

/-! ## 7. The retained spine and the loop exit

Every phase returns to `104`, where the compiled conjunct is pushed onto the
private reverse spine in register `22` and the phase counter advances.  Once
three conjuncts are retained the loop head falls through to `109`, which builds
the fold's constant `true` base case. -/

-- Five steps pushing one compiled conjunct onto the reverse spine.
private theorem run_grammarCaseRetain {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag counter output : ℕ) (values : List ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hspineBits :
      natBitLength (selectiveCountCasesSpineCode (output :: values)) ≤
        maximumBits)
    (hcounterBits : natBitLength (counter + 1) ≤ maximumBits)
    (hpc : machine.pc = 104)
    (houtput : machine.registers 20 = output)
    (hframe :
      GrammarCaseFrame state row caseTag counter
        (selectiveCountCasesSpineCode values) machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 20 →
      GrammarCaseFrame state row caseTag (counter + 1)
        (selectiveCountCasesSpineCode (output :: values)) resumed →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits (5 + extraFuel)
        machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix⟩ := hframe
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hspineForm :
      selectiveCountCasesSpineCode (output :: values) =
        Nat.pair 1 (Nat.pair output (selectiveCountCasesSpineCode values)) :=
    rfl
  have hconsBits :
      natBitLength
          (Nat.pair output (selectiveCountCasesSpineCode values)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  rw [show (5 : ℕ) + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair output (selectiveCountCasesSpineCode values))
    (selectiveGrammarCaseProgram_controllerAt (pc := 104) rfl) hpc
    (by rw [houtput, hspine]) hconsBits]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 105) rfl) rfl
    (hsmall 1 (by omega))]
  rw [run_pair_instruction
    (value := selectiveCountCasesSpineCode (output :: values))
    (selectiveGrammarCaseProgram_controllerAt (pc := 106) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hspineForm])
    hspineBits]
  rw [run_increment_instruction (value := counter + 1)
    (selectiveGrammarCaseProgram_controllerAt (pc := 107) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcounter])
    hcounterBits]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 108) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
  · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
  · simp [NPOracleState.write, NPOracleState.jump, hwidth]
  · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
  · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
  · simp [NPOracleState.write, NPOracleState.jump, hsix]

-- Ten steps from the exhausted loop head to the fold's constant base case.
private theorem run_grammarCaseExit {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag spine : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hframe : GrammarCaseFrame state row caseTag 3 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 113 →
      resumed.registers 23 =
        rawCircuitNodeCode (n := descriptionWidth n bound)
          (.const true) →
      GrammarCaseFrame state row caseTag 3 spine resumed →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits (10 + extraFuel)
        machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix⟩ := hframe
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hnodeForm :
      rawCircuitNodeCode (n := descriptionWidth n bound) (.const true) =
        Nat.pair 0 1 := rfl
  rw [show (10 : ℕ) + extraFuel =
    extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_copy_instruction (value := 3)
    (selectiveGrammarCaseProgram_controllerAt (pc := 20) rfl) hpc
    (by rw [hcounter]) (hsmall 3 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 21) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_decrement_instruction (value := 2)
    (selectiveGrammarCaseProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 2 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 23) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_decrement_instruction (value := 1)
    (selectiveGrammarCaseProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) (hsmall 1 (by omega))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 25) rfl) rfl]
  rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 109) rfl) rfl
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 110) rfl) rfl
    (hsmall 1 (by omega))]
  rw [run_pair_instruction (value := Nat.pair 0 1)
    (selectiveGrammarCaseProgram_controllerAt (pc := 111) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hsmall (Nat.pair 0 1) (by decide))]
  rw [run_branchZero_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 112) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
  · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
  · simp [NPOracleState.write, NPOracleState.jump, hwidth]
  · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
  · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
  · simp [NPOracleState.write, NPOracleState.jump, hcounter]
  · simp [NPOracleState.write, NPOracleState.jump, hspine]
  · simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
  · simp [NPOracleState.write, NPOracleState.jump, hsix]

/-! ## 8. The reverse `and` fold

The exit path emits one conjunction per retained conjunct, innermost first, from
the constant `true` base case.  Interpreter resources are data dependent, so the
fold's clock and its register-width envelope follow the same recursion as its
output. -/

/-- Interpreter fuel of the reverse fold from `125`. -/
private def grammarFoldFuel {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      10 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              grammarFoldFuel (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest)))

/-- Register width of the reverse fold from `125`. -/
private def grammarFoldBits {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | state, accumulated, [] =>
      natBitLength (Nat.pair (selectiveStateCode state) accumulated)
  | state, accumulated, value :: rest =>
      max (natBitLength (selectiveCountCasesSpineCode (value :: rest))) <|
        max
          (natBitLength
            (selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := n) (.and value accumulated)))) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode (selectiveAnd state value accumulated)))) <|
            grammarFoldBits (selectiveAnd state value accumulated).state
              (selectiveAnd state value accumulated).output rest

set_option maxHeartbeats 3200000 in
-- The fold is one induction on the retained spine.
private theorem run_grammarCaseFoldLoop {n bound : ℕ}
    (row : Fin (bound + 1)) (caseTag counter maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (values : List ℕ)
      (state : SelectiveState (descriptionWidth n bound)) (accumulated : ℕ)
      (machine : NPOracleState),
      selectiveStateOrdered state →
      grammarFoldBits state accumulated values ≤ maximumBits →
      machine.pc = 125 →
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated →
      machine.registers 20 = accumulated →
      GrammarCaseFrame state row caseTag counter
        (selectiveCountCasesSpineCode values) machine →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits
          (grammarFoldFuel state accumulated values) machine =
        some
          (selectiveWireCode
            (selectiveUnaryFold state accumulated values)) := by
  intro values
  induction values with
  | nil =>
      intro state accumulated machine _ hbits hpc hwire _ hframe
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hspine, -, -⟩ := hframe
      simp only [grammarFoldBits] at hbits
      simp only [grammarFoldFuel]
      rw [run_branchZero_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 125) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      exact run_halt_instruction (fuel := 0)
        (selectiveGrammarCaseProgram_controllerAt (pc := 135) rfl) rfl
        (by rw [jump_registers_eq, hwire]; rfl) hbits
  | cons value rest inductionHypothesis =>
      intro state accumulated machine hordered hbits hpc hwire houtput hframe
      obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit,
        hwidth, hrowIndex, hcaseTag, hcounter, hspine, hsixPlusLimit, hsix⟩ :=
        hframe
      simp only [grammarFoldBits] at hbits
      have hspineBits := (Nat.le_max_left _ _).trans hbits
      have hbitsOne := (Nat.le_max_right _ _).trans hbits
      have hinputBits := (Nat.le_max_left _ _).trans hbitsOne
      have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
      have hwireBits := (Nat.le_max_left _ _).trans hbitsTwo
      have hrecursiveBits := (Nat.le_max_right _ _).trans hbitsTwo
      have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
        fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
      have hspineForm :
          selectiveCountCasesSpineCode (value :: rest) =
            Nat.pair 1
              (Nat.pair value (selectiveCountCasesSpineCode rest)) := rfl
      have hnodeForm :
          rawCircuitNodeCode (n := descriptionWidth n bound)
              (.and value accumulated) =
            Nat.pair 3
              (Nat.pair (descriptionWidth n bound + value)
                (descriptionWidth n bound + accumulated)) := rfl
      have hemitForm :
          selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.and value accumulated)) =
            Nat.pair (selectiveStateCode state)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.and value accumulated)) := rfl
      have hconsBits :
          natBitLength
              (Nat.pair value (selectiveCountCasesSpineCode rest)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hspineBits
        rw [hspineForm]
        exact Nat.right_le_pair 1 _
      have hvalueBits : natBitLength value ≤ maximumBits :=
        (natBitLength_mono (Nat.left_le_pair _ _)).trans hconsBits
      have htailSpineBits :
          natBitLength (selectiveCountCasesSpineCode rest) ≤ maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans hconsBits
      have hcodeBits :
          natBitLength
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.and value accumulated)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hinputBits
        rw [hemitForm]
        exact Nat.right_le_pair _ _
      have hchildrenBits :
          natBitLength
              (Nat.pair (descriptionWidth n bound + value)
                (descriptionWidth n bound + accumulated)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hcodeBits
        rw [hnodeForm]
        exact Nat.right_le_pair 3 _
      have hleftChildBits :
          natBitLength (descriptionWidth n bound + value) ≤ maximumBits :=
        (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
      have hrightChildBits :
          natBitLength (descriptionWidth n bound + accumulated) ≤ maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
      have hspineNonzero : machine.registers 22 ≠ 0 := by
        rw [hspine, hspineForm]
        have hone :=
          Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
        omega
      simp only [grammarFoldFuel, selectiveUnaryFold]
      rw [show (10 : ℕ) +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                grammarFoldFuel (selectiveAnd state value accumulated).state
                  (selectiveAnd state value accumulated).output rest))) =
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              grammarFoldFuel (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest))) +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 125) rfl) hpc]
      rw [if_neg hspineNonzero]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (selectiveCountCasesSpineCode rest))
        (selectiveGrammarCaseProgram_controllerAt (pc := 126) rfl) rfl
        (by rw [jump_registers_eq, hspine, hspineForm]; simp) hconsBits]
      rw [run_unpairLeft_instruction (value := value)
        (selectiveGrammarCaseProgram_controllerAt (pc := 127) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      rw [run_unpairRight_instruction
        (value := selectiveCountCasesSpineCode rest)
        (selectiveGrammarCaseProgram_controllerAt (pc := 128) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
      rw [run_add_instruction (value := descriptionWidth n bound + value)
        (selectiveGrammarCaseProgram_controllerAt (pc := 129) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity])
        hleftChildBits]
      rw [run_add_instruction (value := descriptionWidth n bound + accumulated)
        (selectiveGrammarCaseProgram_controllerAt (pc := 130) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity, houtput])
        hrightChildBits]
      rw [run_pair_instruction
        (value :=
          Nat.pair (descriptionWidth n bound + value)
            (descriptionWidth n bound + accumulated))
        (selectiveGrammarCaseProgram_controllerAt (pc := 131) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
      rw [run_set_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 132) rfl) rfl
        (hsmall 3 (by omega))]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := descriptionWidth n bound)
            (.and value accumulated))
        (selectiveGrammarCaseProgram_controllerAt (pc := 133) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
        hcodeBits]
      rw [run_branchZero_instruction
        (selectiveGrammarCaseProgram_controllerAt (pc := 134) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveGrammarCaseEmitCall state (.and value accumulated)
        hordered maximumBits _ _ _ (descriptionWidth n bound)
        (row.val * rowWidth n bound) (boundedCircuitFieldLimit n bound) n
        row.val caseTag counter (selectiveCountCasesSpineCode rest)
        (6 + boundedCircuitFieldLimit n bound) 6 _ rfl hinputBits hwireBits rfl
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
      · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
      · simp [NPOracleState.write, NPOracleState.jump, hwidth]
      · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
      · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
      · simp [NPOracleState.write, NPOracleState.jump, hcounter]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, hsixPlusLimit]
      · simp [NPOracleState.write, NPOracleState.jump, hsix]
      · intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
          hresumedSelected hresumedOutput hresumedArity hresumedRowBase
          hresumedFieldLimit hresumedWidth hresumedRowIndex hresumedCaseTag
          hresumedCounter hresumedSpine hresumedSixPlus hresumedSix
        exact inductionHypothesis (selectiveAnd state value accumulated).state
          (selectiveAnd state value accumulated).output resumed
          (selectiveState_emit_ordered state (.and value accumulated) hordered)
          hrecursiveBits hresumedPc hresumedWire hresumedOutput
          ⟨hresumedRemaining, hresumedNext, hresumedSelected, hresumedArity,
            hresumedRowBase, hresumedFieldLimit, hresumedWidth,
            hresumedRowIndex, hresumedCaseTag, hresumedCounter, hresumedSpine,
            hresumedSixPlus, hresumedSix⟩

/-! ## 9. The request parser and the level runner

Twenty straight-line steps parse the request into the frame of §6; §9 feeds the
forward pass from there and packages the whole level in the runner shape §4
publishes. -/

set_option maxHeartbeats 1600000 in
-- Twenty unpacking steps set up the loop's registers.
private theorem run_grammarCasePrologue {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (entry : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveGrammarCaseInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val caseTag) ≤
        maximumBits)
    (hsixPlusBits :
      natBitLength (6 + boundedCircuitFieldLimit n bound) ≤ maximumBits)
    (hpc : entry.pc = 0)
    (hinput :
      entry.registers 0 =
        selectiveGrammarCaseInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val caseTag)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 20 →
      GrammarCaseFrame state row caseTag 0
        (selectiveCountCasesSpineCode []) resumed →
      runNPOracleProgram selectiveGrammarCaseProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveGrammarCaseProgram maximumBits (20 + extraFuel)
        entry =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveGrammarCaseInput] at hflat
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
  have hrowIndexBits := natBitLength_pair_left hfive
  have hcaseTagBits := natBitLength_pair_right hfive
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show (20 : ℕ) + extraFuel =
    extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveGrammarCaseProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveGrammarCaseInput]) hstateBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (descriptionWidth n bound) <|
        Nat.pair (row.val * rowWidth n bound) <|
          Nat.pair (boundedCircuitFieldLimit n bound) <|
            Nat.pair n (Nat.pair row.val caseTag))
    (selectiveGrammarCaseProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveGrammarCaseInput])
    hone]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveGrammarCaseProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveGrammarCaseProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveGrammarCaseProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveGrammarCaseProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairLeft_instruction (value := descriptionWidth n bound)
    (selectiveGrammarCaseProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound) <|
        Nat.pair (boundedCircuitFieldLimit n bound) <|
          Nat.pair n (Nat.pair row.val caseTag))
    (selectiveGrammarCaseProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [run_unpairLeft_instruction (value := row.val * rowWidth n bound)
    (selectiveGrammarCaseProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowBaseBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound) <|
        Nat.pair n (Nat.pair row.val caseTag))
    (selectiveGrammarCaseProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [run_unpairLeft_instruction (value := boundedCircuitFieldLimit n bound)
    (selectiveGrammarCaseProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair n (Nat.pair row.val caseTag))
    (selectiveGrammarCaseProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [run_unpairLeft_instruction (value := n)
    (selectiveGrammarCaseProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction (value := Nat.pair row.val caseTag)
    (selectiveGrammarCaseProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [run_unpairLeft_instruction (value := row.val)
    (selectiveGrammarCaseProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowIndexBits]
  rw [run_unpairRight_instruction (value := caseTag)
    (selectiveGrammarCaseProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcaseTagBits]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 16) rfl) rfl
    (hsmall 6 (by omega))]
  rw [run_add_instruction (value := 6 + boundedCircuitFieldLimit n bound)
    (selectiveGrammarCaseProgram_controllerAt (pc := 17) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsixPlusBits]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 18) rfl) rfl
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveGrammarCaseProgram_controllerAt (pc := 19) rfl) rfl
    (hsmall 0 (by omega))]
  refine hcontinue _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump,
      selectiveCountCasesSpineCode]

/-- The wire the tag test compiles. -/
private def grammarWireZero {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr state (tagEqualsExpr (n := n) row caseTag)

/-- The wire the middle conjunct compiles. -/
private def grammarWireOne {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr (grammarWireZero state row caseTag).state
    (selectiveGrammarCaseFirstField (n := n) row row.val caseTag)

/-- The wire the last conjunct compiles. -/
private def grammarWireTwo {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr (grammarWireOne state row caseTag).state
    (selectiveGrammarCaseSecondField (n := n) row row.val caseTag)

/-- The fold's constant base case. -/
private def grammarBaseWire {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : SelectiveWire (descriptionWidth n bound) :=
  selectiveConst (grammarWireTwo state row caseTag).state true

/-- The retained reverse spine at the loop exit. -/
private def grammarSpine {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : List ℕ :=
  [(grammarWireTwo state row caseTag).output,
    (grammarWireOne state row caseTag).output,
    (grammarWireZero state row caseTag).output]

/-- Interpreter fuel of one whole grammar-case compilation. -/
def selectiveGrammarCaseRunFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : ℕ :=
  20 +
    grammarPhaseZeroFuel state row caseTag
      (5 +
        grammarPhaseOneFuel (grammarWireZero state row caseTag).state row
          caseTag
          (5 +
            grammarPhaseTwoFuel (grammarWireOne state row caseTag).state row
              caseTag
              (5 +
                (10 +
                  (5 +
                    (selectiveEmitFuel
                        ((grammarWireTwo state row caseTag).state.target -
                          (grammarWireTwo state row caseTag).state.next)
                        (selectiveSelectedCode
                          (grammarWireTwo state row caseTag).state.selected) +
                      (7 +
                        grammarFoldFuel
                          (grammarBaseWire state row caseTag).state
                          (grammarBaseWire state row caseTag).output
                          (grammarSpine state row caseTag))))))))

/-- Register width of one whole grammar-case compilation. -/
def selectiveGrammarCaseRunBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) : ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveGrammarCaseInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val caseTag)) <|
      max (natBitLength (6 + boundedCircuitFieldLimit n bound)) <|
        max (grammarPhaseZeroBits state row caseTag) <|
          max
            (grammarPhaseOneBits (grammarWireZero state row caseTag).state row
              caseTag) <|
            max
              (grammarPhaseTwoBits (grammarWireOne state row caseTag).state row
                caseTag) <|
              max
                (natBitLength
                  (selectiveCountCasesSpineCode
                    [(grammarWireZero state row caseTag).output])) <|
                max
                  (natBitLength
                    (selectiveCountCasesSpineCode
                      [(grammarWireOne state row caseTag).output,
                        (grammarWireZero state row caseTag).output])) <|
                  max
                    (natBitLength
                      (selectiveCountCasesSpineCode
                        (grammarSpine state row caseTag))) <|
                    max
                      (natBitLength
                        (selectiveEmitInput
                          ((grammarWireTwo state row caseTag).state.target -
                            (grammarWireTwo state row caseTag).state.next)
                          (grammarWireTwo state row caseTag).state.next
                          (selectiveSelectedCode
                            (grammarWireTwo state row caseTag).state.selected)
                          (rawCircuitNodeCode
                            (n := descriptionWidth n bound) (.const true)))) <|
                      max
                        (natBitLength
                          (Nat.pair 0
                            (selectiveWireCode
                              (grammarBaseWire state row caseTag)))) <|
                        grammarFoldBits (grammarBaseWire state row caseTag).state
                          (grammarBaseWire state row caseTag).output
                          (grammarSpine state row caseTag)

set_option maxHeartbeats 1600000 in
-- Twenty parser steps, three dispatched phases and the reverse fold.
/-- **The grammar-case compiler's run.**  The `446`-instruction stream started
on its own ABI frame, at any entry registers, returns exactly the compiler wire
the source compiler produces for the scheduled grammar row case. -/
theorem run_selectiveGrammarCaseProgram {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag : ℕ)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveGrammarCaseInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val caseTag) :
    runNPOracleProgram selectiveGrammarCaseProgram
        (selectiveGrammarCaseRunBits state row caseTag)
        (selectiveGrammarCaseRunFuel state row caseTag) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag))) := by
  have hbits :
      selectiveGrammarCaseRunBits state row caseTag ≤
        selectiveGrammarCaseRunBits state row caseTag := le_refl _
  unfold selectiveGrammarCaseRunBits at hbits
  have hsevenBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hsixPlusBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hphaseZeroBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have hphaseOneBits := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hphaseTwoBits := (Nat.le_max_left _ _).trans hbitsFive
  have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
  have hspineZeroBits := (Nat.le_max_left _ _).trans hbitsSix
  have hbitsSeven := (Nat.le_max_right _ _).trans hbitsSix
  have hspineOneBits := (Nat.le_max_left _ _).trans hbitsSeven
  have hbitsEight := (Nat.le_max_right _ _).trans hbitsSeven
  have hspineTwoBits := (Nat.le_max_left _ _).trans hbitsEight
  have hbitsNine := (Nat.le_max_right _ _).trans hbitsEight
  have hemitInputBits := (Nat.le_max_left _ _).trans hbitsNine
  have hbitsTen := (Nat.le_max_right _ _).trans hbitsNine
  have hemitWireBits := (Nat.le_max_left _ _).trans hbitsTen
  have hfoldBits := (Nat.le_max_right _ _).trans hbitsTen
  have hsmall : ∀ value : ℕ, value ≤ 7 →
      natBitLength value ≤ selectiveGrammarCaseRunBits state row caseTag :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have horderedOne : selectiveStateOrdered (grammarWireZero state row caseTag).state :=
    selectiveCompileExpr_ordered state _ hordered
  have horderedTwo : selectiveStateOrdered (grammarWireOne state row caseTag).state :=
    selectiveCompileExpr_ordered _ _ horderedOne
  have horderedThree :
      selectiveStateOrdered (grammarWireTwo state row caseTag).state :=
    selectiveCompileExpr_ordered _ _ horderedTwo
  rw [selectiveGrammarCaseExpr_eq_fold]
  unfold selectiveGrammarCaseRunFuel
  refine run_grammarCasePrologue state row caseTag _ _ _ entry hsevenBits
    hrequestBits hsixPlusBits hentryPc hentryInput ?_
  intro afterPrologue hprologuePc hprologueFrame
  refine run_grammarCasePhaseZero state row caseTag hordered _ _ _ _
    afterPrologue hsevenBits hphaseZeroBits hprologuePc hprologueFrame ?_
  intro afterZero hzeroPc hzeroOutput hzeroFrame
  refine run_grammarCaseRetain (grammarWireZero state row caseTag).state row
    caseTag 0 (grammarWireZero state row caseTag).output [] _ _ _ afterZero
    hsevenBits hspineZeroBits (hsmall 1 (by omega)) hzeroPc hzeroOutput
    hzeroFrame ?_
  intro afterRetainZero hretainZeroPc hretainZeroFrame
  refine run_grammarCasePhaseOne (grammarWireZero state row caseTag).state row
    caseTag horderedOne _ _ _ _ afterRetainZero hsevenBits hphaseOneBits
    hretainZeroPc hretainZeroFrame ?_
  intro afterOne honePc honeOutput honeFrame
  refine run_grammarCaseRetain (grammarWireOne state row caseTag).state row
    caseTag 1 (grammarWireOne state row caseTag).output
    [(grammarWireZero state row caseTag).output] _ _ _ afterOne hsevenBits
    hspineOneBits (hsmall 2 (by omega)) honePc honeOutput honeFrame ?_
  intro afterRetainOne hretainOnePc hretainOneFrame
  refine run_grammarCasePhaseTwo (grammarWireOne state row caseTag).state row
    caseTag horderedTwo _ _ _ _ afterRetainOne hsevenBits hphaseTwoBits
    hretainOnePc hretainOneFrame ?_
  intro afterTwo htwoPc htwoOutput htwoFrame
  refine run_grammarCaseRetain (grammarWireTwo state row caseTag).state row
    caseTag 2 (grammarWireTwo state row caseTag).output
    [(grammarWireOne state row caseTag).output,
      (grammarWireZero state row caseTag).output] _ _ _ afterTwo hsevenBits
    hspineTwoBits (hsmall 3 (by omega)) htwoPc htwoOutput htwoFrame ?_
  intro afterRetainTwo hretainTwoPc hretainTwoFrame
  refine run_grammarCaseExit (grammarWireTwo state row caseTag).state row
    caseTag _ _ _ _ afterRetainTwo hsevenBits hretainTwoPc hretainTwoFrame ?_
  intro afterExit hexitPc hexitNode hexitFrame
  obtain ⟨hexitRemaining, hexitNext, hexitSelected, hexitArity, hexitRowBase,
    hexitFieldLimit, hexitWidth, hexitRowIndex, hexitCaseTag, hexitCounter,
    hexitSpine, hexitSixPlus, hexitSix⟩ := hexitFrame
  refine run_selectiveGrammarCaseEmitCall
    (grammarWireTwo state row caseTag).state (.const true) horderedThree _ _ _ _
    (descriptionWidth n bound) (row.val * rowWidth n bound)
    (boundedCircuitFieldLimit n bound) n row.val caseTag 3
    (selectiveCountCasesSpineCode (grammarSpine state row caseTag))
    (6 + boundedCircuitFieldLimit n bound) 6 afterExit rfl hemitInputBits
    hemitWireBits hexitPc hexitRemaining hexitNext hexitSelected hexitNode
    hexitArity hexitRowBase hexitFieldLimit hexitWidth hexitRowIndex
    hexitCaseTag hexitCounter hexitSpine hexitSixPlus hexitSix ?_
  intro afterBase hbasePc hbaseWire hbaseRemaining hbaseNext hbaseSelected
    hbaseOutput hbaseArity hbaseRowBase hbaseFieldLimit hbaseWidth
    hbaseRowIndex hbaseCaseTag hbaseCounter hbaseSpine hbaseSixPlus hbaseSix
  exact run_grammarCaseFoldLoop row caseTag 3 _ hsevenBits
    (grammarSpine state row caseTag) (grammarBaseWire state row caseTag).state
    (grammarBaseWire state row caseTag).output afterBase
    (selectiveState_emit_ordered _ _ horderedThree) hfoldBits hbasePc hbaseWire
    hbaseOutput
    ⟨hbaseRemaining, hbaseNext, hbaseSelected, hbaseArity, hbaseRowBase,
      hbaseFieldLimit, hbaseWidth, hbaseRowIndex, hbaseCaseTag, hbaseCounter,
      hbaseSpine, hbaseSixPlus, hbaseSix⟩

/-- **Level premise, discharged.**  The grammar-case compiler's run at its own
ABI frame, packaged in the runner shape the node-row scheduler one level up
consumes.  Nothing on this level is left as a premise. -/
def selectiveGrammarCaseRunner (width bound : ℕ) :
    SelectiveGrammarCaseRunner width bound where
  bits state row caseTag := selectiveGrammarCaseRunBits state row caseTag
  fuel state row caseTag := selectiveGrammarCaseRunFuel state row caseTag
  executes := by
    intro state row caseTag hordered entry hentryPc hentryInput
    exact run_selectiveGrammarCaseProgram state row caseTag hordered entry
      hentryPc hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
