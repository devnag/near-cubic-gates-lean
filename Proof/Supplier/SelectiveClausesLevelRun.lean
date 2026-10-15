import Proof.Supplier.SelectiveClauseLevelRun

/-!
# Level 10 of the nested structural compiler: the clause-list compiler

`selectiveClausesProgram` is the `335`-instruction stream that compiles a whole
decoded clause list and its right-associated `and` suffix.  Its `68`-instruction
controller relocates three callees — the clause compiler of level 11, the
spine-length fold and the append transition.

`SelectiveClauseRun` §4 fixes the scheduling identity
(`selectiveCompileClauses_eq_fold`), §10–§11 execute the shared append block and
the reverse conjunction fold outright, §12 executes one iteration of the forward
clause pass from the level-11 premise, and §13 inhabits the schedule that pass
walks.  Everything below is the forward-loop induction over that schedule plus
the eighteen-step request parser.

The literal arity is the row's query count, and the source decoder returns an
empty clause list whenever it is zero while the controller reads its clause
count from the decision code itself; the level therefore carries the same
`0 < literalArity` side condition the outer-proof row stages already carry.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open private selectiveCompileClause_ordered
  from Proof.Supplier.SelectiveCountCasesRun

open private selectiveClausesProgram selectiveClausesControllerProgram
  selectiveClausesControllerProgram_length selectiveClausesInput
  selectiveClauseInput selectiveClauseProgram
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 0. The controller's zero register at an arbitrary entry state

Unlike the clause controller of level 11, this controller never writes register
`29`: every one of its unconditional back edges is a `branchZero 29 t t`, whose
two targets coincide, so the register's entry value is irrelevant.  The level's
published shape, however, quantifies over *every* entry state, and the four
blocks `SelectiveClauseRun` §10–§12 prove all pin that register at zero purely
to thread it through their continuations.  The four statements below are those
blocks with the pinned value released; nothing else changes, and each proof is
the original one verbatim.
-/

private theorem run_selectiveClausesEmitCallAt {n zeroRegister : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity values literalArity decisionCode count clauseIndex spine : ℕ)
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
    (hpc : machine.pc = 45)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 23 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = spine)
    (hzeroRegister : machine.registers 29 = zeroRegister)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 57 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 2 = selectiveStateCode (state.emit node).state →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 20 = (state.emit node).output →
      resumed.registers 8 = arity →
      resumed.registers 10 = values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = count →
      resumed.registers 17 = clauseIndex →
      resumed.registers 18 = spine →
      resumed.registers 29 = zeroRegister →
      runNPOracleProgram selectiveClausesProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClausesProgram maximumBits
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
    (selectiveClausesProgram_controllerAt (pc := 45) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveClausesProgram_controllerAt (pc := 46) rfl) rfl
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
    (selectiveClausesProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 48) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 49) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveClausesProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
      (selectiveClausesProgram_controllerAt (pc := 50) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveClausesProgram_controllerAt (pc := 51) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveClausesProgram_controllerAt (pc := 52) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (state.emit node).state.target - (state.emit node).state.next)
      (selectiveClausesProgram_controllerAt (pc := 53) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveClausesProgram_controllerAt (pc := 54) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveClausesProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveClausesProgram_controllerAt (pc := 56) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hvalues, hliteralArity, hdecisionCode, hcount, hclauseIndex, hspine,
        hzeroRegister]

private theorem run_selectiveClausesFoldStepAt {n zeroRegister : ℕ}
    (state : SelectiveState n) (accumulated value : ℕ) (rest : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (values literalArity decisionCode count clauseIndex : ℕ)
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
            (rawCircuitNodeCode (n := n) (.and value accumulated))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode (selectiveAnd state value accumulated))) ≤
        maximumBits)
    (hpc : machine.pc = 57)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine :
      machine.registers 18 = selectiveCountCasesSpineCode (value :: rest))
    (haccumulated : machine.registers 20 = accumulated)
    (hzeroRegister : machine.registers 29 = zeroRegister)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 57 →
      resumed.registers 0 =
        selectiveWireCode (selectiveAnd state value accumulated) →
      resumed.registers 4 =
        (selectiveAnd state value accumulated).state.target -
          (selectiveAnd state value accumulated).state.next →
      resumed.registers 6 = (selectiveAnd state value accumulated).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveAnd state value accumulated).state.selected →
      resumed.registers 8 = n →
      resumed.registers 10 = values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = count →
      resumed.registers 17 = clauseIndex →
      resumed.registers 18 = selectiveCountCasesSpineCode rest →
      resumed.registers 20 = (selectiveAnd state value accumulated).output →
      resumed.registers 29 = zeroRegister →
      runNPOracleProgram selectiveClausesProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (10 + (5 + (emitFuel + (7 + extraFuel)))) machine =
      some finalOutput := by
  have hnodeCode :
      rawCircuitNodeCode (n := n) (.and value accumulated) =
        Nat.pair 3 (Nat.pair (n + value) (n + accumulated)) := rfl
  have hemitInput :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.and value accumulated)) =
        Nat.pair (selectiveStateCode state)
          (rawCircuitNodeCode (n := n) (.and value accumulated)) := rfl
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
      natBitLength (rawCircuitNodeCode (n := n) (.and value accumulated)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hinputBits
    rw [hemitInput]
    exact Nat.right_le_pair _ _
  have hchildrenBits :
      natBitLength (Nat.pair (n + value) (n + accumulated)) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.right_le_pair 3 _
  have hleftChildBits : natBitLength (n + value) ≤ maximumBits :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
  have hrightChildBits : natBitLength (n + accumulated) ≤ maximumBits :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
  have hthreeBits : natBitLength 3 ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.left_le_pair 3 _
  have hspineNonzero : machine.registers 18 ≠ 0 := by
    rw [hspine, hspineForm]
    have hone :=
      Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
    omega
  rw [show 10 + (5 + (emitFuel + (7 + extraFuel))) =
    (9 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 57) rfl) hpc]
  rw [if_neg hspineNonzero]
  rw [show 9 + (5 + (emitFuel + (7 + extraFuel))) =
    (8 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair value (selectiveCountCasesSpineCode rest))
    (selectiveClausesProgram_controllerAt (pc := 58) rfl) rfl
    (by simp [NPOracleState.jump, hspine, hspineForm]) hconsBits]
  rw [show 8 + (5 + (emitFuel + (7 + extraFuel))) =
    (7 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_unpairLeft_instruction (value := value)
    (selectiveClausesProgram_controllerAt (pc := 59) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 7 + (5 + (emitFuel + (7 + extraFuel))) =
    (6 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveCountCasesSpineCode rest)
    (selectiveClausesProgram_controllerAt (pc := 60) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
  rw [show 6 + (5 + (emitFuel + (7 + extraFuel))) =
    (5 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_add_instruction (value := n + value)
    (selectiveClausesProgram_controllerAt (pc := 61) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hleftChildBits]
  rw [show 5 + (5 + (emitFuel + (7 + extraFuel))) =
    (4 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_add_instruction (value := n + accumulated)
    (selectiveClausesProgram_controllerAt (pc := 62) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, haccumulated])
    hrightChildBits]
  rw [show 4 + (5 + (emitFuel + (7 + extraFuel))) =
    (3 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + value) (n + accumulated))
    (selectiveClausesProgram_controllerAt (pc := 63) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 3 + (5 + (emitFuel + (7 + extraFuel))) =
    (2 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 64) rfl) rfl hthreeBits]
  rw [show 2 + (5 + (emitFuel + (7 + extraFuel))) =
    (1 + (5 + (emitFuel + (7 + extraFuel)))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.and value accumulated))
    (selectiveClausesProgram_controllerAt (pc := 65) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 1 + (5 + (emitFuel + (7 + extraFuel))) =
    (5 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 66) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveClausesEmitCallAt (zeroRegister := zeroRegister) state
    (.and value accumulated) hordered
    maximumBits emitFuel extraFuel finalOutput n values literalArity
    decisionCode count clauseIndex (selectiveCountCasesSpineCode rest) _
    hemitFuel hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hvalues]
  · simp [NPOracleState.write, NPOracleState.jump, hliteralArity]
  · simp [NPOracleState.write, NPOracleState.jump, hdecisionCode]
  · simp [NPOracleState.write, NPOracleState.jump, hcount]
  · simp [NPOracleState.write, NPOracleState.jump, hclauseIndex]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, hzeroRegister]
  · intro resumed hresumedPc hresumedWire _ hresumedRemaining hresumedNext
      hresumedSelected hresumedOutput hresumedArity hresumedValues
      hresumedLiteralArity hresumedDecisionCode hresumedCount
      hresumedClauseIndex hresumedSpine hresumedZero
    refine hcontinue resumed hresumedPc ?_ ?_ ?_ ?_ hresumedArity hresumedValues
      hresumedLiteralArity hresumedDecisionCode hresumedCount
      hresumedClauseIndex hresumedSpine ?_ hresumedZero
    · simpa [selectiveAnd] using hresumedWire
    · simpa [selectiveAnd] using hresumedRemaining
    · simpa [selectiveAnd] using hresumedNext
    · simpa [selectiveAnd] using hresumedSelected
    · simpa [selectiveAnd] using hresumedOutput

private theorem run_selectiveClausesFoldLoopAt {n zeroRegister : ℕ}
    (spineValues : List ℕ) (state : SelectiveState n) (accumulated : ℕ)
    (hordered : selectiveStateOrdered state) (maximumBits : ℕ)
    (hbits :
      natBitLength
          (selectiveUnaryFoldWorkBound state accumulated spineValues) ≤
        maximumBits)
    (values literalArity decisionCode count clauseIndex : ℕ)
    (machine : NPOracleState) (hpc : machine.pc = 57)
    (hwire :
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode spineValues)
    (haccumulated : machine.registers 20 = accumulated)
    (hzeroRegister : machine.registers 29 = zeroRegister) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (selectiveClausesFoldFuel state accumulated spineValues) machine =
      some
        (selectiveWireCode
          (selectiveUnaryFold state accumulated spineValues)) := by
  induction spineValues generalizing state accumulated machine with
  | nil =>
      have hfuel :
          selectiveClausesFoldFuel state accumulated ([] : List ℕ) =
            (0 + 1) + 1 := rfl
      have hfoldNil :
          selectiveWireCode
              (selectiveUnaryFold state accumulated ([] : List ℕ)) =
            Nat.pair (selectiveStateCode state) accumulated := rfl
      rw [hfuel]
      rw [run_branchZero_instruction
        (selectiveClausesProgram_controllerAt (pc := 57) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      refine run_halt_instruction (fuel := 0)
        (selectiveClausesProgram_controllerAt (pc := 67) rfl) rfl ?_ ?_
      · rw [hfoldNil]
        exact hwire
      · rw [hfoldNil]
        exact hbits
  | cons value rest ih =>
      have hfuel :
          selectiveClausesFoldFuel state accumulated (value :: rest) =
            10 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    selectiveClausesFoldFuel
                      (selectiveAnd state value accumulated).state
                      (selectiveAnd state value accumulated).output
                      rest))) := rfl
      have hworkCons :
          selectiveUnaryFoldWorkBound state accumulated (value :: rest) =
            max (selectiveCountCasesSpineCode (value :: rest))
              (max
                (selectiveEmitInput (state.target - state.next) state.next
                  (selectiveSelectedCode state.selected)
                  (rawCircuitNodeCode (n := n) (.and value accumulated)))
                (max
                  (Nat.pair 0
                    (selectiveWireCode (selectiveAnd state value accumulated)))
                  (selectiveUnaryFoldWorkBound
                    (selectiveAnd state value accumulated).state
                    (selectiveAnd state value accumulated).output rest))) := rfl
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
      refine run_selectiveClausesFoldStepAt (zeroRegister := zeroRegister) state
        accumulated value rest hordered
        maximumBits _ _ _ values literalArity decisionCode count clauseIndex
        machine rfl hspineBits hinputBits hwireBits hpc hremaining hnext
        hselected harity hvalues hliteralArity hdecisionCode hcount
        hclauseIndex hspine haccumulated hzeroRegister ?_
      intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedValues hresumedLiteralArity
        hresumedDecisionCode hresumedCount hresumedClauseIndex hresumedSpine
        hresumedAccumulated hresumedZero
      exact ih _ _
        (selectiveState_emit_ordered state (.and value accumulated) hordered)
        hrecBits _ hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedValues hresumedLiteralArity
        hresumedDecisionCode hresumedCount hresumedClauseIndex hresumedSpine
        hresumedAccumulated hresumedZero

private theorem run_selectiveClausesForwardStepAt {n literalArity zeroRegister : ℕ}
    {harity : 0 < literalArity}
    (runner : SelectiveClauseRunner n literalArity harity)
    (state : SelectiveState n) (values : List ℕ)
    (decisionCode clauseIndex count : ℕ) (spine : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hcalleeFuel :
      calleeFuel = runner.fuel state values decisionCode clauseIndex)
    (hcalleeBits :
      runner.bits state values decisionCode clauseIndex ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveClauseInput (selectiveStateCode state) n
            (encodeTaggedList values) literalArity decisionCode clauseIndex) ≤
        maximumBits)
    (hheadBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileClause state values
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex)))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveCompileClause state values
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex)).output :: spine)) ≤
        maximumBits)
    (hindexSuccBits : natBitLength (clauseIndex + 1) ≤ maximumBits)
    (hcountBits : natBitLength count ≤ maximumBits)
    (hcountNonzero : count ≠ 0)
    (hpc : machine.pc = 18)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harityRegister : machine.registers 8 = n)
    (hvalues : machine.registers 10 = encodeTaggedList values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hcount : machine.registers 16 = count)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode spine)
    (hzeroRegister : machine.registers 29 = zeroRegister)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 =
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.target -
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.next →
      resumed.registers 6 =
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.selected →
      resumed.registers 8 = n →
      resumed.registers 10 = encodeTaggedList values →
      resumed.registers 12 = literalArity →
      resumed.registers 14 = decisionCode →
      resumed.registers 16 = Nat.pred count →
      resumed.registers 17 = clauseIndex + 1 →
      resumed.registers 18 =
        selectiveCountCasesSpineCode
          ((selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).output :: spine) →
      resumed.registers 29 = zeroRegister →
      runNPOracleProgram selectiveClausesProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (10 + (calleeFuel + (13 + extraFuel))) machine =
      some finalOutput := by
  have hstateForm : ∀ candidate : SelectiveState n,
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestFlat := hrequestBits
  simp only [selectiveClauseInput] at hrequestFlat
  have hstateBits := natBitLength_pair_left hrequestFlat
  have hfield1 := natBitLength_pair_right hrequestFlat
  have hfield2 := natBitLength_pair_right hfield1
  have hfield3 := natBitLength_pair_right hfield2
  have hfield4 := natBitLength_pair_right hfield3
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hheadFlat := natBitLength_pair_right hheadBits
  have hheadParts := hheadFlat
  simp only [selectiveWireCode] at hheadParts
  have hheadStateBits := natBitLength_pair_left hheadParts
  have hheadOutputBits := natBitLength_pair_right hheadParts
  have hheadStateFlat := hheadStateBits
  rw [hstateForm
    (selectiveCompileClause state values
      (selectiveClauseOf literalArity harity decisionCode
        clauseIndex)).state] at hheadStateFlat
  have hheadRemainingBits := natBitLength_pair_left hheadStateFlat
  have hheadTailBits := natBitLength_pair_right hheadStateFlat
  have hheadNextBits := natBitLength_pair_left hheadTailBits
  have hheadSelectedBits := natBitLength_pair_right hheadTailBits
  have hspineFlat := hspineBits
  simp only [selectiveCountCasesSpineCode] at hspineFlat
  have honeBits := natBitLength_pair_left hspineFlat
  have hconsBits := natBitLength_pair_right hspineFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le 1)).trans honeBits
  have hnextCountBits : natBitLength (Nat.pred count) ≤ maximumBits :=
    (decrement_bits_le count).trans hcountBits
  rw [show 10 + (calleeFuel + (13 + extraFuel)) =
    (9 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_neg (by rw [hcount]; exact hcountNonzero)]
  rw [show 9 + (calleeFuel + (13 + extraFuel)) =
    (8 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveClausesProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.jump, hnext, hselected]) hnextSelectedBits]
  rw [show 8 + (calleeFuel + (13 + extraFuel)) =
    (7 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveClausesProgram_controllerAt (pc := 20) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 7 + (calleeFuel + (13 + extraFuel)) =
    (6 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair decisionCode clauseIndex)
    (selectiveClausesProgram_controllerAt (pc := 21) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hdecisionCode,
        hclauseIndex])
    hfield4]
  rw [show 6 + (calleeFuel + (13 + extraFuel)) =
    (5 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair literalArity (Nat.pair decisionCode clauseIndex))
    (selectiveClausesProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hliteralArity]) hfield3]
  rw [show 5 + (calleeFuel + (13 + extraFuel)) =
    (4 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeTaggedList values)
        (Nat.pair literalArity (Nat.pair decisionCode clauseIndex)))
    (selectiveClausesProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hvalues]) hfield2]
  rw [show 4 + (calleeFuel + (13 + extraFuel)) =
    (3 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair n
        (Nat.pair (encodeTaggedList values)
          (Nat.pair literalArity (Nat.pair decisionCode clauseIndex))))
    (selectiveClausesProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harityRegister]) hfield1]
  rw [show 3 + (calleeFuel + (13 + extraFuel)) =
    (2 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveClauseInput (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode clauseIndex)
    (selectiveClausesProgram_controllerAt (pc := 25) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectiveClauseInput])
    hrequestBits]
  rw [show 2 + (calleeFuel + (13 + extraFuel)) =
    (1 + (calleeFuel + (13 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 26) rfl) rfl hzeroBits]
  rw [show 1 + (calleeFuel + (13 + extraFuel)) =
    (calleeFuel + (13 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 27) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveClauseProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode clauseIndex)))
    selectiveClausesProgram_clauseCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro entry hentryPc hentryInput
    refine run_bits_mono
      (runner.executes state values decisionCode clauseIndex hordered entry
        hentryPc ?_) hcalleeBits
    rw [hentryInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hheadBits
  · intro haltState
    rw [show (13 : ℕ) + extraFuel = (12 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode clauseIndex)))
      (selectiveClausesProgram_controllerAt (pc := 28) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadFlat]
    rw [show (12 : ℕ) + extraFuel = (11 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state)
      (selectiveClausesProgram_controllerAt (pc := 29) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hheadStateBits]
    rw [show (11 : ℕ) + extraFuel = (10 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).output)
      (selectiveClausesProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hheadOutputBits]
    rw [show (10 : ℕ) + extraFuel = (9 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.target -
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.next)
      (selectiveClausesProgram_controllerAt (pc := 31) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm
            (selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).state])
      hheadRemainingBits]
    rw [show (9 : ℕ) + extraFuel = (8 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.next
          (selectiveSelectedCode
            (selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).state.selected))
      (selectiveClausesProgram_controllerAt (pc := 32) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm
            (selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).state])
      hheadTailBits]
    rw [show (8 : ℕ) + extraFuel = (7 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileClause state values
          (selectiveClauseOf literalArity harity decisionCode
            clauseIndex)).state.next)
      (selectiveClausesProgram_controllerAt (pc := 33) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadNextBits]
    rw [show (7 : ℕ) + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).state.selected)
      (selectiveClausesProgram_controllerAt (pc := 34) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadSelectedBits]
    rw [show (6 : ℕ) + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair
          (selectiveCompileClause state values
            (selectiveClauseOf literalArity harity decisionCode
              clauseIndex)).output (selectiveCountCasesSpineCode spine))
      (selectiveClausesProgram_controllerAt (pc := 35) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine])
      hconsBits]
    rw [show (5 : ℕ) + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_set_instruction
      (selectiveClausesProgram_controllerAt (pc := 36) rfl) rfl honeBits]
    rw [show (4 : ℕ) + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        selectiveCountCasesSpineCode
          ((selectiveCompileClause state values
              (selectiveClauseOf literalArity harity decisionCode
                clauseIndex)).output :: spine))
      (selectiveClausesProgram_controllerAt (pc := 37) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          selectiveCountCasesSpineCode])
      hspineBits]
    rw [show (3 : ℕ) + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_increment_instruction (value := clauseIndex + 1)
      (selectiveClausesProgram_controllerAt (pc := 38) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hclauseIndex])
      hindexSuccBits]
    rw [show (2 : ℕ) + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := Nat.pred count)
      (selectiveClausesProgram_controllerAt (pc := 39) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hcount])
      hnextCountBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveClausesProgram_controllerAt (pc := 40) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState,
        harityRegister, hvalues, hliteralArity, hdecisionCode, hzeroRegister]

/-! ## 1. The wire the forward loop head produces -/

/-- Compiler wire the controller produces from the clause loop head: every
remaining clause compiled forward, then the whole retained spine folded. -/
private def selectiveClausesForwardOutput {q n : ℕ} (state : SelectiveState n)
    (values : List ℕ) (clauses : List (Fin 3 → Literal q)) (spine : List ℕ) :
    SelectiveWire n :=
  selectiveUnaryFold
    (selectiveConst (selectiveClausesHeads state values clauses).state
      true).state
    (selectiveConst (selectiveClausesHeads state values clauses).state
      true).output
    ((selectiveClausesHeads state values clauses).values.reverse ++ spine)

private theorem selectiveClausesForwardOutput_cons {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ) (clause : Fin 3 → Literal q)
    (rest : List (Fin 3 → Literal q)) (spine : List ℕ) :
    selectiveClausesForwardOutput state values (clause :: rest) spine =
      selectiveClausesForwardOutput
        (selectiveCompileClause state values clause).state values rest
        ((selectiveCompileClause state values clause).output :: spine) := by
  simp only [selectiveClausesForwardOutput, selectiveClausesHeads,
    List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem selectiveClausesForwardOutput_empty {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (clauses : List (Fin 3 → Literal q)) :
    selectiveClausesForwardOutput state values clauses [] =
      selectiveCompileClauses state values clauses := by
  rw [selectiveCompileClauses_eq_fold]
  simp only [selectiveClausesForwardOutput, List.append_nil]

/-! ## 2. The loop's exit: the explicit `true` base case and the reverse fold -/

/-- Register width of the clause loop's exit. -/
private def selectiveClausesTailBits {n : ℕ} (state : SelectiveState n)
    (spine : List ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected)
        (rawCircuitNodeCode (n := n) (.const true)))) <|
    max
      (natBitLength (Nat.pair 0 (selectiveWireCode (selectiveConst state true))))
      (natBitLength
        (selectiveUnaryFoldWorkBound (selectiveConst state true).state
          (selectiveConst state true).output spine))

/-- Interpreter fuel of the clause loop's exit. -/
private def selectiveClausesTailFuel {n : ℕ} (state : SelectiveState n)
    (spine : List ℕ) : ℕ :=
  1 +
    (4 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine))))

set_option maxHeartbeats 1600000 in
-- Four controller steps around the relocated append, then the reverse fold.
private theorem run_selectiveClausesTail {n zeroRegister : ℕ}
    (state : SelectiveState n)
    (spineValues : List ℕ) (hordered : selectiveStateOrdered state)
    (maximumBits values literalArity decisionCode clauseIndex : ℕ)
    (machine : NPOracleState)
    (hbits : selectiveClausesTailBits state spineValues ≤ maximumBits)
    (hpc : machine.pc = 18)
    (hcount : machine.registers 16 = 0)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hvalues : machine.registers 10 = values)
    (hliteralArity : machine.registers 12 = literalArity)
    (hdecisionCode : machine.registers 14 = decisionCode)
    (hclauseIndex : machine.registers 17 = clauseIndex)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode spineValues)
    (hzeroRegister : machine.registers 29 = zeroRegister) :
    runNPOracleProgram selectiveClausesProgram maximumBits
        (selectiveClausesTailFuel state spineValues) machine =
      some
        (selectiveWireCode
          (selectiveUnaryFold (selectiveConst state true).state
            (selectiveConst state true).output spineValues)) := by
  rw [selectiveClausesTailBits] at hbits
  have hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.const true))) ≤ maximumBits :=
    (Nat.le_max_left _ _).trans hbits
  have hbitsTail := (Nat.le_max_right _ _).trans hbits
  have hwireBits :
      natBitLength
          (Nat.pair 0 (selectiveWireCode (selectiveConst state true))) ≤
        maximumBits := (Nat.le_max_left _ _).trans hbitsTail
  have hfoldBits :
      natBitLength
          (selectiveUnaryFoldWorkBound (selectiveConst state true).state
            (selectiveConst state true).output spineValues) ≤ maximumBits :=
    (Nat.le_max_right _ _).trans hbitsTail
  have hnodeForm :
      rawCircuitNodeCode (n := n) (.const true) = Nat.pair 0 1 := rfl
  have hnodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.const true)) ≤ maximumBits :=
    natBitLength_pair_right hinputBits
  have hnodeFlat := hnodeBits
  rw [hnodeForm] at hnodeFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    natBitLength_pair_left hnodeFlat
  have honeBits : natBitLength 1 ≤ maximumBits :=
    natBitLength_pair_right hnodeFlat
  rw [selectiveClausesTailFuel]
  rw [show 1 +
      (4 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              selectiveClausesFoldFuel (selectiveConst state true).state
                (selectiveConst state true).output spineValues)))) =
    (4 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_pos (by rw [hcount])]
  rw [show 4 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues))) =
    (3 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues)))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 41) rfl) rfl hzeroBits]
  rw [show 3 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues))) =
    (2 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues)))) + 1 by omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 42) rfl) rfl honeBits]
  rw [show 2 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues))) =
    (1 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues)))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.const true))
    (selectiveClausesProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm]) hnodeBits]
  rw [show 1 +
      (5 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 +
            selectiveClausesFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spineValues))) =
    (5 +
      (selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected) +
        (7 +
          selectiveClausesFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spineValues))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 44) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveClausesEmitCallAt (zeroRegister := zeroRegister) state
    (.const true) hordered maximumBits _
    _ _ n values literalArity decisionCode 0 clauseIndex
    (selectiveCountCasesSpineCode spineValues) _ rfl hinputBits hwireBits ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · simp [NPOracleState.write, NPOracleState.jump, hremaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump, hnodeForm]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hvalues]
  · simp [NPOracleState.write, NPOracleState.jump, hliteralArity]
  · simp [NPOracleState.write, NPOracleState.jump, hdecisionCode]
  · simp [NPOracleState.write, NPOracleState.jump, hcount]
  · simp [NPOracleState.write, NPOracleState.jump, hclauseIndex]
  · simp [NPOracleState.write, NPOracleState.jump, hspine]
  · simp [NPOracleState.write, NPOracleState.jump, hzeroRegister]
  · intro resumed hresumedPc hresumedWire _hresumedState hresumedRemaining
      hresumedNext hresumedSelected hresumedOutput hresumedArity hresumedValues
      hresumedLiteralArity hresumedDecisionCode hresumedCount
      hresumedClauseIndex hresumedSpine hresumedZero
    exact run_selectiveClausesFoldLoopAt (zeroRegister := zeroRegister) spineValues
      (selectiveConst state true).state (selectiveConst state true).output
      (selectiveState_emit_ordered state (.const true) hordered) maximumBits
      hfoldBits values literalArity decisionCode 0 clauseIndex resumed
      hresumedPc hresumedWire hresumedRemaining hresumedNext hresumedSelected
      hresumedArity hresumedValues hresumedLiteralArity hresumedDecisionCode
      hresumedCount hresumedClauseIndex hresumedSpine hresumedOutput
      hresumedZero

/-! ## 3. The forward clause pass -/

/-- Register width of the whole forward clause pass and its exit. -/
private def selectiveClausesForwardBits {n literalArity : ℕ}
    (harity : 0 < literalArity)
    (runner : SelectiveClauseRunner n literalArity harity) (values : List ℕ)
    (decisionCode : ℕ) :
    SelectiveState n → ℕ → List (Fin 3 → Literal literalArity) → List ℕ → ℕ
  | state, _clauseIndex, [], spine => selectiveClausesTailBits state spine
  | state, clauseIndex, _clause :: rest, spine =>
      max (runner.bits state values decisionCode clauseIndex) <|
        max
          (natBitLength
            (selectiveClauseInput (selectiveStateCode state) n
              (encodeTaggedList values) literalArity decisionCode
              clauseIndex)) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveCompileClause state values
                    (selectiveClauseOf literalArity harity decisionCode
                      clauseIndex))))) <|
            max
              (natBitLength
                (selectiveCountCasesSpineCode
                  ((selectiveCompileClause state values
                      (selectiveClauseOf literalArity harity decisionCode
                        clauseIndex)).output :: spine))) <|
              selectiveClausesForwardBits harity runner values decisionCode
                (selectiveCompileClause state values
                  (selectiveClauseOf literalArity harity decisionCode
                    clauseIndex)).state
                (clauseIndex + 1) rest
                ((selectiveCompileClause state values
                  (selectiveClauseOf literalArity harity decisionCode
                    clauseIndex)).output :: spine)

/-- Interpreter fuel of the whole forward clause pass and its exit. -/
private def selectiveClausesForwardFuel {n literalArity : ℕ}
    (harity : 0 < literalArity)
    (runner : SelectiveClauseRunner n literalArity harity) (values : List ℕ)
    (decisionCode : ℕ) :
    SelectiveState n → ℕ → List (Fin 3 → Literal literalArity) → List ℕ → ℕ
  | state, _clauseIndex, [], spine => selectiveClausesTailFuel state spine
  | state, clauseIndex, _clause :: rest, spine =>
      10 +
        (runner.fuel state values decisionCode clauseIndex +
          (13 +
            selectiveClausesForwardFuel harity runner values decisionCode
              (selectiveCompileClause state values
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex)).state
              (clauseIndex + 1) rest
              ((selectiveCompileClause state values
                (selectiveClauseOf literalArity harity decisionCode
                  clauseIndex)).output :: spine)))

set_option maxHeartbeats 1600000 in
-- The forward pass is one induction on the clause schedule; its exit emits the
-- base `true` and chains straight into the reverse fold.
private theorem run_selectiveClausesForwardLoop {n literalArity zeroRegister : ℕ}
    {harity : 0 < literalArity}
    (runner : SelectiveClauseRunner n literalArity harity) (values : List ℕ)
    (decisionCode : ℕ) :
    ∀ {clauseIndex : ℕ} {clauses : List (Fin 3 → Literal literalArity)},
      SelectiveClausesFrom literalArity harity decisionCode clauseIndex
        clauses →
      ∀ (state : SelectiveState n) (spine : List ℕ) (maximumBits : ℕ)
        (machine : NPOracleState),
      selectiveStateOrdered state →
      selectiveClausesForwardBits harity runner values decisionCode state
          clauseIndex clauses spine ≤
        maximumBits →
      natBitLength clauses.length ≤ maximumBits →
      natBitLength (clauseIndex + clauses.length) ≤ maximumBits →
      machine.pc = 18 →
      machine.registers 4 = state.target - state.next →
      machine.registers 6 = state.next →
      machine.registers 7 = selectiveSelectedCode state.selected →
      machine.registers 8 = n →
      machine.registers 10 = encodeTaggedList values →
      machine.registers 12 = literalArity →
      machine.registers 14 = decisionCode →
      machine.registers 16 = clauses.length →
      machine.registers 17 = clauseIndex →
      machine.registers 18 = selectiveCountCasesSpineCode spine →
      machine.registers 29 = zeroRegister →
      runNPOracleProgram selectiveClausesProgram maximumBits
          (selectiveClausesForwardFuel harity runner values decisionCode state
            clauseIndex clauses spine)
          machine =
        some
          (selectiveWireCode
            (selectiveClausesForwardOutput state values clauses spine)) := by
  intro clauseIndex clauses hclauses
  induction hclauses with
  | nil clauseIndex =>
      intro state spine maximumBits machine hordered hbits _hcountBits
        _hindexBits hpc hremaining hnext hselected harity hvalues hliteralArity
        hdecisionCode hcount hclauseIndex hspine hzeroRegister
      exact run_selectiveClausesTail state spine hordered maximumBits
        (encodeTaggedList values) literalArity decisionCode clauseIndex machine
        hbits hpc (by simpa using hcount) hremaining hnext hselected harity
        hvalues hliteralArity hdecisionCode hclauseIndex hspine hzeroRegister
  | cons hrest inductionHypothesis =>
      rename_i clauseIndex rest
      intro state spine maximumBits machine hordered hbits hcountBits hindexBits
        hpc hremaining hnext hselected harityRegister hvalues hliteralArity
        hdecisionCode hcount hclauseIndex hspine hzeroRegister
      rw [selectiveClausesForwardBits] at hbits
      have hcalleeBits := (Nat.le_max_left _ _).trans hbits
      have hbitsOne := (Nat.le_max_right _ _).trans hbits
      have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
      have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
      have hheadBits := (Nat.le_max_left _ _).trans hbitsTwo
      have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
      have hspineBits := (Nat.le_max_left _ _).trans hbitsThree
      have hrecBits := (Nat.le_max_right _ _).trans hbitsThree
      have hlength :
          (selectiveClauseOf literalArity harity decisionCode clauseIndex ::
            rest).length = rest.length + 1 := rfl
      have hindexSuccBits : natBitLength (clauseIndex + 1) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hindexBits
        rw [hlength]
        omega
      have hrestCountBits : natBitLength rest.length ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hcountBits
        rw [hlength]
        omega
      have hrestIndexBits :
          natBitLength (clauseIndex + 1 + rest.length) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hindexBits
        rw [hlength]
        omega
      rw [selectiveClausesForwardFuel, selectiveClausesForwardOutput_cons]
      refine run_selectiveClausesForwardStepAt (zeroRegister := zeroRegister) runner
        state values decisionCode
        clauseIndex (rest.length + 1) spine hordered maximumBits _ _ _ machine
        rfl hcalleeBits hrequestBits hheadBits hspineBits hindexSuccBits
        (by simpa [hlength] using hcountBits) (by omega) hpc hremaining hnext
        hselected harityRegister hvalues hliteralArity hdecisionCode
        (by simpa [hlength] using hcount) hclauseIndex hspine hzeroRegister ?_
      intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedArity hresumedValues hresumedLiteralArity hresumedDecisionCode
        hresumedCount hresumedClauseIndex hresumedSpine hresumedZero
      exact inductionHypothesis _ _ maximumBits resumed
        (selectiveCompileClause_ordered state values _ hordered) hrecBits
        hrestCountBits hrestIndexBits hresumedPc hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedValues hresumedLiteralArity
        hresumedDecisionCode (by simpa using hresumedCount) hresumedClauseIndex
        hresumedSpine hresumedZero

/-! ## 4. The whole `335`-instruction stream -/

/-- Register width of one whole clause-list compilation. -/
def selectiveClausesRunBits {n literalArity : ℕ} (harity : 0 < literalArity)
    (runner : SelectiveClauseRunner n literalArity harity)
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveClausesInput (selectiveStateCode state) n
        (encodeTaggedList values) literalArity decisionCode)) <|
    max (encodedListLengthBits decisionCode) <|
      max (natBitLength (Nat.pair 0 (encodedListLength decisionCode)))
        (selectiveClausesForwardBits harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses [])

/-- Interpreter fuel of one whole clause-list compilation. -/
def selectiveClausesRunFuel {n literalArity : ℕ} (harity : 0 < literalArity)
    (runner : SelectiveClauseRunner n literalArity harity)
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ) : ℕ :=
  15 +
    (encodedListLengthFuel decisionCode +
      (3 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses []))

set_option maxHeartbeats 1600000 in
-- The eighteen-step request parser runs the spine-length fold in the middle and
-- feeds the clause loop head.
/-- **Level 10's run.**  The `335`-instruction clause-list compiler started on
its own ABI frame, at any entry registers, returns exactly the source compiler's
wire for the whole decoded clause list. -/
theorem run_selectiveClausesProgram {n literalArity : ℕ}
    (harity : 0 < literalArity)
    (runner : SelectiveClauseRunner n literalArity harity)
    (state : SelectiveState n) (values : List ℕ) (decisionCode : ℕ)
    (hordered : selectiveStateOrdered state) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveClausesInput (selectiveStateCode state) n
          (encodeTaggedList values) literalArity decisionCode) :
    runNPOracleProgram selectiveClausesProgram
        (selectiveClausesRunBits harity runner state values decisionCode)
        (selectiveClausesRunFuel harity runner state values decisionCode)
        entry =
      some
        (selectiveWireCode
          (selectiveCompileClauses state values
            (decodeThreeCNF literalArity decisionCode).clauses)) := by
  have hrequestBits :
      natBitLength
          (selectiveClausesInput (selectiveStateCode state) n
            (encodeTaggedList values) literalArity decisionCode) ≤
        selectiveClausesRunBits harity runner state values decisionCode := by
    unfold selectiveClausesRunBits
    omega
  have hlengthBits :
      encodedListLengthBits decisionCode ≤
        selectiveClausesRunBits harity runner state values decisionCode := by
    unfold selectiveClausesRunBits
    omega
  have hcountPairBits :
      natBitLength (Nat.pair 0 (encodedListLength decisionCode)) ≤
        selectiveClausesRunBits harity runner state values decisionCode := by
    unfold selectiveClausesRunBits
    omega
  have hforwardBits :
      selectiveClausesForwardBits harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses [] ≤
        selectiveClausesRunBits harity runner state values decisionCode := by
    unfold selectiveClausesRunBits
    omega
  have hcountEq :
      encodedListLength decisionCode =
        (decodeThreeCNF literalArity decisionCode).clauses.length :=
    encodedListLength_eq_decodeThreeCNF_clauses literalArity decisionCode harity
  have hcountBits :
      natBitLength (decodeThreeCNF literalArity decisionCode).clauses.length ≤
        selectiveClausesRunBits harity runner state values decisionCode := by
    rw [← hcountEq]
    exact natBitLength_pair_right hcountPairBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveClausesInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hfieldOne := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hfieldOne
  have hfieldTwo := natBitLength_pair_right hfieldOne
  have hvaluesBits := natBitLength_pair_left hfieldTwo
  have hfieldThree := natBitLength_pair_right hfieldTwo
  have hliteralArityBits := natBitLength_pair_left hfieldThree
  have hdecisionBits := natBitLength_pair_right hfieldThree
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailBits
  have hselectedBits := natBitLength_pair_right htailBits
  have hzeroBits :
      natBitLength 0 ≤
        selectiveClausesRunBits harity runner state values decisionCode :=
    (natBitLength_mono (Nat.zero_le _)).trans hstateBits
  rw [← selectiveClausesForwardOutput_empty state values
    (decodeThreeCNF literalArity decisionCode).clauses]
  rw [selectiveClausesRunFuel]
  rw [show 15 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (14 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveClausesProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, selectiveClausesInput]) hstateBits]
  rw [show 14 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (13 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair n
        (Nat.pair (encodeTaggedList values)
          (Nat.pair literalArity decisionCode)))
    (selectiveClausesProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveClausesInput])
    hfieldOne]
  rw [show 13 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (12 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveClausesProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 12 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (11 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveClausesProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailBits]
  rw [show 11 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (10 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveClausesProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 10 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (9 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveClausesProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [show 9 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (8 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := n)
    (selectiveClausesProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 8 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (7 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (encodeTaggedList values) (Nat.pair literalArity decisionCode))
    (selectiveClausesProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldTwo]
  rw [show 7 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (6 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := encodeTaggedList values)
    (selectiveClausesProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvaluesBits]
  rw [show 6 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (5 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair literalArity decisionCode)
    (selectiveClausesProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldThree]
  rw [show 5 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (4 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := literalArity)
    (selectiveClausesProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hliteralArityBits]
  rw [show 4 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (3 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_unpairRight_instruction (value := decisionCode)
    (selectiveClausesProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdecisionBits]
  rw [show 3 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (2 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_copy_instruction (value := decisionCode)
    (selectiveClausesProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hdecisionBits]
  rw [show 2 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (1 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses []))) + 1 by
    omega]
  rw [run_set_instruction
    (selectiveClausesProgram_controllerAt (pc := 13) rfl) rfl hzeroBits]
  rw [show 1 +
      (encodedListLengthFuel decisionCode +
        (3 +
          selectiveClausesForwardFuel harity runner values decisionCode state 0
            (decodeThreeCNF literalArity decisionCode).clauses [])) =
    (encodedListLengthFuel decisionCode +
      (3 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses [])) + 1 by
    omega]
  rw [run_branchZero_instruction
    (selectiveClausesProgram_controllerAt (pc := 14) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveRelocatedCall
    (source := encodedListLengthProgram)
    (calleeOutput := encodedListLength decisionCode)
    selectiveClausesProgram_lengthCallable (by omega) rfl ?_ ?_
    hcountPairBits ?_
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_encodedListLengthProgram_anyEntry decisionCode frame hframePc ?_)
      hlengthBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro lengthHalt
    rw [show 3 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses [] =
      (2 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses []) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := (decodeThreeCNF literalArity decisionCode).clauses.length)
      (selectiveClausesProgram_controllerAt (pc := 15) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hcountEq]) hcountBits]
    rw [show 2 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses [] =
      (1 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses []) + 1 by omega]
    rw [run_set_instruction
      (selectiveClausesProgram_controllerAt (pc := 16) rfl) rfl hzeroBits]
    rw [show 1 +
        selectiveClausesForwardFuel harity runner values decisionCode state 0
          (decodeThreeCNF literalArity decisionCode).clauses [] =
      selectiveClausesForwardFuel harity runner values decisionCode state 0
        (decodeThreeCNF literalArity decisionCode).clauses [] + 1 by omega]
    rw [run_set_instruction
      (selectiveClausesProgram_controllerAt (pc := 17) rfl) rfl hzeroBits]
    refine run_selectiveClausesForwardLoop (zeroRegister := entry.registers 29)
      runner values decisionCode
      (selectiveClausesFrom_zero literalArity harity decisionCode) state []
      _ _ hordered hforwardBits hcountBits (by simpa using hcountBits) rfl ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState,
        selectiveCountCasesSpineCode]

/-! ## 5. The level premise, discharged -/

/-- **`SelectiveClausesRunner`, discharged.**  Level 10 owes nothing beyond the
row's own query-count positivity: the whole clause-list compiler runs at its own
ABI frame for every ordered state, every live wire list and every decision
code. -/
def selectiveClausesRunner (n literalArity : ℕ) (harity : 0 < literalArity) :
    SelectiveClausesRunner n literalArity where
  bits := fun state values decisionCode =>
    selectiveClausesRunBits harity (selectiveClauseRunner n literalArity harity)
      state values decisionCode
  fuel := fun state values decisionCode =>
    selectiveClausesRunFuel harity (selectiveClauseRunner n literalArity harity)
      state values decisionCode
  executes := by
    intro state values decisionCode hordered entry hentryPc hentryInput
    exact run_selectiveClausesProgram harity
      (selectiveClauseRunner n literalArity harity) state values decisionCode
      hordered entry hentryPc hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
