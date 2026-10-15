import Proof.Supplier.SelectiveGrammarCaseRun
import Batteries.Tactic.OpenPrivate

/-!
# The node-row compiler's run

`selectiveNodeRowProgram` is the `534`-instruction stream that compiles one
description row's node-row predicate: a controller of `70` instructions with
two relocated callees, the `446`-instruction grammar-case compiler and the
`18`-instruction append transition.

The controller is a five-iteration loop.  Ascending case tags in register `18`
select the grammar row case; the countdown in register `19` falls; the compiled
case outputs stay on one private reverse spine in register `20`.  The exit
emits the canonical `false` base case and folds the spine back into the source
compiler's right-associated disjunction, one append per retained case.

This module executes that controller, discharging the level from
`SelectiveGrammarCaseRun`'s already-closed run alone.
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

open private selectiveGrammarCaseInput selectiveGrammarCaseProgram
  selectiveGrammarCaseProgram_length selectiveNodeRowInput
  selectiveNodeRowControllerProgram selectiveNodeRowControllerProgram_length
  selectiveNodeRowProgram selectiveNodeRowProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The five grammar row cases, at the typed level

The controller's ascending case tags are exactly the five node-row cases of the
source compiler, and its outer `any` is exactly the source compiler's
right-associated disjunction over them. -/

/-- The disjunct schedule the controller walks. -/
def selectiveNodeRowExprs {n bound : ℕ} (row : Fin (bound + 1)) :
    List (BoolExpr (descriptionWidth n bound)) :=
  List.ofFn fun index : Fin 5 =>
    selectiveGrammarCaseExpr (n := n) row row.val index.val

/-- **The controller's schedule, identified with the source compiler's node-row
predicate.** -/
theorem boolExpr_any_selectiveNodeRowExprs {n bound : ℕ}
    (row : Fin (bound + 1)) :
    BoolExpr.any (selectiveNodeRowExprs (n := n) row) =
      nodeRowExpr (n := n) row := by
  rfl

/-! ## 2. Decoding the fixed 534-instruction stream

The controller occupies the first `70` positions, the grammar-case compiler the
next `446` and the append callee the last `18`. -/

private theorem selectiveNodeRowProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveNodeRowControllerProgram 70 516)[pc]? = some instruction) :
    selectiveNodeRowProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveNodeRowControllerProgram 70 516).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveNodeRowControllerProgram_length] at hpc
  simp only [selectiveNodeRowProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveNodeRowControllerProgram_length,
      selectiveGrammarCaseProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveNodeRowControllerProgram_length]
    omega)]
  exact hlookup

private theorem selectiveNodeRowProgram_caseCallable :
    ProgramCallableAt selectiveNodeRowProgram selectiveGrammarCaseProgram
      70 1000 50 30 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveGrammarCaseProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveGrammarCaseProgram_length] at hpc
  simp only [selectiveNodeRowProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveNodeRowControllerProgram_length,
      selectiveGrammarCaseProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveNodeRowControllerProgram_length]
    omega)]
  simp only [selectiveNodeRowControllerProgram_length]
  rw [show 70 + pc - 70 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveNodeRowProgram_emitCallable :
    ProgramCallableAt selectiveNodeRowProgram selectiveEmitProgram
      516 12000 50 52 := by
  intro pc instruction hlookup
  simp only [selectiveNodeRowProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveNodeRowControllerProgram_length,
      selectiveGrammarCaseProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveNodeRowControllerProgram_length,
    selectiveGrammarCaseProgram_length]
  rw [show 516 + pc - (70 + 446) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The controller's live frame and its two call blocks

The loop head at `19`, the retain block at `37` and the fold at `59` all share
one live register frame: the compiler state, the request constants, the case
tag, the countdown and the retained spine. -/

private theorem jump_registers_eq (machine : NPOracleState)
    (target index : ℕ) :
    (machine.jump target).registers index = machine.registers index := rfl

/-- The controller's live register frame. -/
private def NodeRowFrame {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag remaining spine : ℕ) (machine : NPOracleState) : Prop :=
  machine.registers 4 = state.target - state.next ∧
    machine.registers 6 = state.next ∧
      machine.registers 7 = selectiveSelectedCode state.selected ∧
        machine.registers 8 = descriptionWidth n bound ∧
          machine.registers 10 = row.val * rowWidth n bound ∧
            machine.registers 12 = boundedCircuitFieldLimit n bound ∧
              machine.registers 14 = n ∧
                machine.registers 16 = row.val ∧
                  machine.registers 18 = caseTag ∧
                    machine.registers 19 = remaining ∧
                      machine.registers 20 = spine

set_option maxHeartbeats 1600000 in
-- Ten request steps around the relocated grammar-case compiler, then seven
-- unpacking steps.
private theorem run_nodeRowCaseCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag remaining spine : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits caseFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcaseFuel : caseFuel = selectiveGrammarCaseRunFuel state row caseTag)
    (hcalleeBits :
      selectiveGrammarCaseRunBits state row caseTag ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveGrammarCaseInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val caseTag) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileExpr state
                (selectiveGrammarCaseExpr (n := n) row row.val caseTag)))) ≤
        maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 20)
    (hframe : NodeRowFrame state row caseTag remaining spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 37 →
      resumed.registers 22 =
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output →
      NodeRowFrame
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state row
        caseTag remaining spine resumed →
      runNPOracleProgram selectiveNodeRowProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveNodeRowProgram maximumBits
        (10 + (caseFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcount, hspine⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveGrammarCaseInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val caseTag =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (descriptionWidth n bound)
            (Nat.pair (row.val * rowWidth n bound)
              (Nat.pair (boundedCircuitFieldLimit n bound)
                (Nat.pair n (Nat.pair row.val caseTag))))) := rfl
  have hflat := hrequestBits
  rw [hrequestForm] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hfive := natBitLength_pair_right hfour
  have hstateFlat := hstateBits
  rw [hstateForm state] at hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
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
  rw [show 10 + (caseFuel + (7 + extraFuel)) =
    (caseFuel + (7 + extraFuel)) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by
    omega]
  rw [run_pair_instruction (value := Nat.pair row.val caseTag)
    (selectiveNodeRowProgram_controllerAt (pc := 20) rfl) hpc
    (by rw [hrowIndex, hcaseTag]) hfive]
  rw [run_pair_instruction (value := Nat.pair n (Nat.pair row.val caseTag))
    (selectiveNodeRowProgram_controllerAt (pc := 21) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfour]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound)
        (Nat.pair n (Nat.pair row.val caseTag)))
    (selectiveNodeRowProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hthree]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair (boundedCircuitFieldLimit n bound)
          (Nat.pair n (Nat.pair row.val caseTag))))
    (selectiveNodeRowProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htwo]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair (boundedCircuitFieldLimit n bound)
            (Nat.pair n (Nat.pair row.val caseTag)))))
    (selectiveNodeRowProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveNodeRowProgram_controllerAt (pc := 25) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveNodeRowProgram_controllerAt (pc := 26) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveGrammarCaseInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound)
        (boundedCircuitFieldLimit n bound) n row.val caseTag)
    (selectiveNodeRowProgram_controllerAt (pc := 27) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 28) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 29) rfl) rfl]
  simp only [ite_self]
  rw [hcaseFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveGrammarCaseProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)))
    selectiveNodeRowProgram_caseCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveGrammarCaseProgram state row caseTag hordered frame
        hframePc ?_) hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _caseHalt
    rw [show 7 + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)))
      (selectiveNodeRowProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state)
      (selectiveNodeRowProgram_controllerAt (pc := 31) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output)
      (selectiveNodeRowProgram_controllerAt (pc := 32) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state.target -
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state.next)
      (selectiveNodeRowProgram_controllerAt (pc := 33) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state.next
          (selectiveSelectedCode
            (selectiveCompileExpr state
              (selectiveGrammarCaseExpr (n := n) row row.val
                caseTag)).state.selected))
      (selectiveNodeRowProgram_controllerAt (pc := 34) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state.next)
      (selectiveNodeRowProgram_controllerAt (pc := 35) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val
              caseTag)).state.selected)
      (selectiveNodeRowProgram_controllerAt (pc := 36) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hfieldLimit, hwidth, hrowIndex, hcaseTag, hcount, hspine]

-- Three request steps around the relocated append, then seven unpacking steps.
private theorem run_nodeRowEmitCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (node : BooleanNode (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag remaining spine : ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected) (rawCircuitNodeCode node)) ≤
        maximumBits)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode (state.emit node))) ≤
        maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 47)
    (hnode : machine.registers 23 = rawCircuitNodeCode node)
    (hframe : NodeRowFrame state row caseTag remaining spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 59 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 22 = (state.emit node).output →
      NodeRowFrame (state.emit node).state row caseTag remaining spine
        resumed →
      runNPOracleProgram selectiveNodeRowProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveNodeRowProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcount, hspine⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
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
    (emitFuel + (7 + extraFuel)) + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveNodeRowProgram_controllerAt (pc := 47) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveNodeRowProgram_controllerAt (pc := 48) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveNodeRowProgram_controllerAt (pc := 49) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 50) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 51) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveNodeRowProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
    rw [show 7 + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (state.emit node))
      (selectiveNodeRowProgram_controllerAt (pc := 52) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveNodeRowProgram_controllerAt (pc := 53) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveNodeRowProgram_controllerAt (pc := 54) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [run_unpairLeft_instruction
      (value := (state.emit node).state.target - (state.emit node).state.next)
      (selectiveNodeRowProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveNodeRowProgram_controllerAt (pc := 56) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveNodeRowProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveNodeRowProgram_controllerAt (pc := 58) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hfieldLimit, hwidth, hrowIndex, hcaseTag, hcount, hspine]

/-! ## 4. One loop iteration and the loop exit -/

-- One iteration: the loop test, §3's call block, and six steps threading the
-- spine, the case tag and the countdown.
private theorem run_nodeRowIteration {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag remaining : ℕ) (values : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits caseFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcaseFuel : caseFuel = selectiveGrammarCaseRunFuel state row caseTag)
    (hcalleeBits :
      selectiveGrammarCaseRunBits state row caseTag ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveGrammarCaseInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val caseTag) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileExpr state
                (selectiveGrammarCaseExpr (n := n) row row.val caseTag)))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveCompileExpr state
              (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output ::
              values)) ≤
        maximumBits)
    (hcaseTagBits : natBitLength (caseTag + 1) ≤ maximumBits)
    (hcountBits : natBitLength remaining ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hpc : machine.pc = 19)
    (hframe :
      NodeRowFrame state row caseTag (remaining + 1)
        (selectiveCountCasesSpineCode values) machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 19 →
      NodeRowFrame
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).state row
        (caseTag + 1) remaining
        (selectiveCountCasesSpineCode
          ((selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output ::
            values)) resumed →
      runNPOracleProgram selectiveNodeRowProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveNodeRowProgram maximumBits
        (1 + (10 + (caseFuel + (7 + (6 + extraFuel))))) machine =
      some finalOutput := by
  have hcountReg := hframe.2.2.2.2.2.2.2.2.2.1
  have hspineForm :
      selectiveCountCasesSpineCode
          ((selectiveCompileExpr state
            (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output ::
            values) =
        Nat.pair 1
          (Nat.pair
            (selectiveCompileExpr state
              (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output
            (selectiveCountCasesSpineCode values)) := rfl
  have hconsBits :
      natBitLength
          (Nat.pair
            (selectiveCompileExpr state
              (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output
            (selectiveCountCasesSpineCode values)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  rw [show 1 + (10 + (caseFuel + (7 + (6 + extraFuel)))) =
    (10 + (caseFuel + (7 + (6 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 19) rfl) hpc]
  rw [if_neg (by rw [hcountReg]; omega)]
  refine run_nodeRowCaseCall state row caseTag (remaining + 1)
    (selectiveCountCasesSpineCode values) hordered maximumBits caseFuel _
    finalOutput _ hcaseFuel hcalleeBits hrequestBits hwireBits hzeroBits rfl
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [jump_registers_eq]; exact hframe.1
  · rw [jump_registers_eq]; exact hframe.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.2.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.2.2.2.2.2.1
  · rw [jump_registers_eq]; exact hframe.2.2.2.2.2.2.2.2.2.2
  intro middle hmiddlePc hmiddleOutput hmiddleFrame
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcount, hspine⟩ := hmiddleFrame
  rw [show 6 + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output
        (selectiveCountCasesSpineCode values))
    (selectiveNodeRowProgram_controllerAt (pc := 37) rfl) hmiddlePc
    (by rw [hmiddleOutput, hspine]) hconsBits]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 38) rfl) rfl honeBits]
  rw [run_pair_instruction
    (value :=
      selectiveCountCasesSpineCode
        ((selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output ::
          values))
    (selectiveNodeRowProgram_controllerAt (pc := 39) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hspineForm])
    hspineBits]
  rw [run_increment_instruction (value := caseTag + 1)
    (selectiveNodeRowProgram_controllerAt (pc := 40) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcaseTag])
    hcaseTagBits]
  rw [run_decrement_instruction (value := remaining)
    (selectiveNodeRowProgram_controllerAt (pc := 41) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcount]) hcountBits]
  rw [run_branchZero_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 42) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext,
      hselected, harity, hrowBase, hfieldLimit, hwidth, hrowIndex]

-- Five steps from the exhausted loop head to the fold's constant base case.
private theorem run_nodeRowExit {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (caseTag spine : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 19)
    (hframe : NodeRowFrame state row caseTag 0 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 47 →
      resumed.registers 23 =
        rawCircuitNodeCode (n := descriptionWidth n bound) (.const false) →
      NodeRowFrame state row caseTag 0 spine resumed →
      runNPOracleProgram selectiveNodeRowProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveNodeRowProgram maximumBits (5 + extraFuel)
        machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit, hwidth,
    hrowIndex, hcaseTag, hcount, hspine⟩ := hframe
  have hnodeForm :
      rawCircuitNodeCode (n := descriptionWidth n bound) (.const false) =
        Nat.pair 0 0 := rfl
  rw [show 5 + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 19) rfl) hpc]
  rw [if_pos hcount]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 43) rfl) rfl hzeroBits]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 44) rfl) rfl hzeroBits]
  rw [run_pair_instruction (value := Nat.pair 0 0)
    (selectiveNodeRowProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by rw [show Nat.pair 0 0 = 0 from rfl]; exact hzeroBits)]
  rw [run_branchZero_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 46) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext,
      hselected, harity, hrowBase, hfieldLimit, hwidth, hrowIndex, hcaseTag,
      hcount, hspine]

/-! ## 5. The reverse `or` fold

The exit path emits one disjunction per retained case, innermost first, from the
constant `false` base case.  Interpreter resources are data dependent, so the
fold's clock and its register-width envelope follow the same recursion as its
output. -/

/-- Interpreter fuel of the reverse fold from `59`. -/
private def nodeRowFoldFuel {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      10 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              nodeRowFoldFuel (selectiveOr state value accumulated).state
                (selectiveOr state value accumulated).output rest)))

/-- Register width of the reverse fold from `59`. -/
private def nodeRowFoldBits {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | state, accumulated, [] =>
      natBitLength (Nat.pair (selectiveStateCode state) accumulated)
  | state, accumulated, value :: rest =>
      max (natBitLength (selectiveCountCasesSpineCode (value :: rest))) <|
        max
          (natBitLength
            (selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := n) (.or value accumulated)))) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode (selectiveOr state value accumulated)))) <|
            nodeRowFoldBits (selectiveOr state value accumulated).state
              (selectiveOr state value accumulated).output rest

set_option maxHeartbeats 3200000 in
-- The fold is one induction on the retained spine.
private theorem run_nodeRowFoldLoop {n bound : ℕ}
    (row : Fin (bound + 1)) (caseTag maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (values : List ℕ)
      (state : SelectiveState (descriptionWidth n bound)) (accumulated : ℕ)
      (machine : NPOracleState),
      selectiveStateOrdered state →
      nodeRowFoldBits state accumulated values ≤ maximumBits →
      machine.pc = 59 →
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated →
      machine.registers 22 = accumulated →
      NodeRowFrame state row caseTag 0
        (selectiveCountCasesSpineCode values) machine →
      runNPOracleProgram selectiveNodeRowProgram maximumBits
          (nodeRowFoldFuel state accumulated values) machine =
        some
          (selectiveWireCode
            (selectiveCountCasesFold state accumulated values)) := by
  intro values
  induction values with
  | nil =>
      intro state accumulated machine _ hbits hpc hwire _ hframe
      simp only [nodeRowFoldBits] at hbits
      simp only [nodeRowFoldFuel]
      rw [run_branchZero_instruction
        (selectiveNodeRowProgram_controllerAt (pc := 59) rfl) hpc]
      rw [if_pos (by rw [hframe.2.2.2.2.2.2.2.2.2.2]; rfl)]
      exact run_halt_instruction (fuel := 0)
        (selectiveNodeRowProgram_controllerAt (pc := 69) rfl) rfl
        (by rw [jump_registers_eq, hwire]; rfl) hbits
  | cons value rest inductionHypothesis =>
      intro state accumulated machine hordered hbits hpc hwire houtput hframe
      obtain ⟨hremaining, hnext, hselected, harity, hrowBase, hfieldLimit,
        hwidth, hrowIndex, hcaseTag, hcount, hspine⟩ := hframe
      simp only [nodeRowFoldBits] at hbits
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
              (.or value accumulated) =
            Nat.pair 4
              (Nat.pair (descriptionWidth n bound + value)
                (descriptionWidth n bound + accumulated)) := rfl
      have hemitForm :
          selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.or value accumulated)) =
            Nat.pair (selectiveStateCode state)
              (rawCircuitNodeCode (n := descriptionWidth n bound)
                (.or value accumulated)) := rfl
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
                (.or value accumulated)) ≤
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
        exact Nat.right_le_pair 4 _
      have hleftChildBits :
          natBitLength (descriptionWidth n bound + value) ≤ maximumBits :=
        (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
      have hrightChildBits :
          natBitLength (descriptionWidth n bound + accumulated) ≤ maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
      have hspineNonzero : machine.registers 20 ≠ 0 := by
        rw [hspine, hspineForm]
        have hone :=
          Nat.left_le_pair 1
            (Nat.pair value (selectiveCountCasesSpineCode rest))
        omega
      simp only [nodeRowFoldFuel, selectiveCountCasesFold]
      rw [show (10 : ℕ) +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                nodeRowFoldFuel (selectiveOr state value accumulated).state
                  (selectiveOr state value accumulated).output rest))) =
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              nodeRowFoldFuel (selectiveOr state value accumulated).state
                (selectiveOr state value accumulated).output rest))) +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveNodeRowProgram_controllerAt (pc := 59) rfl) hpc]
      rw [if_neg hspineNonzero]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (selectiveCountCasesSpineCode rest))
        (selectiveNodeRowProgram_controllerAt (pc := 60) rfl) rfl
        (by rw [jump_registers_eq, hspine, hspineForm]; simp) hconsBits]
      rw [run_unpairLeft_instruction (value := value)
        (selectiveNodeRowProgram_controllerAt (pc := 61) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      rw [run_unpairRight_instruction
        (value := selectiveCountCasesSpineCode rest)
        (selectiveNodeRowProgram_controllerAt (pc := 62) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
      rw [run_add_instruction (value := descriptionWidth n bound + value)
        (selectiveNodeRowProgram_controllerAt (pc := 63) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity])
        hleftChildBits]
      rw [run_add_instruction (value := descriptionWidth n bound + accumulated)
        (selectiveNodeRowProgram_controllerAt (pc := 64) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity, houtput])
        hrightChildBits]
      rw [run_pair_instruction
        (value :=
          Nat.pair (descriptionWidth n bound + value)
            (descriptionWidth n bound + accumulated))
        (selectiveNodeRowProgram_controllerAt (pc := 65) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
      rw [run_set_instruction
        (selectiveNodeRowProgram_controllerAt (pc := 66) rfl) rfl
        (hsmall 4 (by omega))]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := descriptionWidth n bound)
            (.or value accumulated))
        (selectiveNodeRowProgram_controllerAt (pc := 67) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
        hcodeBits]
      rw [run_branchZero_instruction
        (selectiveNodeRowProgram_controllerAt (pc := 68) rfl) rfl]
      simp only [ite_self]
      refine run_nodeRowEmitCall state (.or value accumulated) row caseTag 0
        (selectiveCountCasesSpineCode rest) hordered maximumBits _ _ _ _ rfl
        hinputBits hwireBits (hsmall 0 (by omega)) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
      · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
      · simp [NPOracleState.write, NPOracleState.jump, hwidth]
      · simp [NPOracleState.write, NPOracleState.jump, hrowIndex]
      · simp [NPOracleState.write, NPOracleState.jump, hcaseTag]
      · simp [NPOracleState.write, NPOracleState.jump, hcount]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedWire hresumedOutput hresumedFrame
        exact inductionHypothesis (selectiveOr state value accumulated).state
          (selectiveOr state value accumulated).output resumed
          (selectiveState_emit_ordered state (.or value accumulated) hordered)
          hrecursiveBits hresumedPc hresumedWire hresumedOutput hresumedFrame

/-! ## 6. The request parser and the level runner

The last component of the request is a padding slot: this controller unpacks it
into a register it never reads again.  Callers one level up build the request
from their own spare frame register, which nothing zeroes, so the parser is
stated at an arbitrary padding value and the published request is that
statement at padding zero. -/

/-- The node-row request with an arbitrary trailing padding component. -/
def selectiveNodeRowPaddedInput
    (stateCode inputArity rowBase fieldLimit width rowIndex padding : ℕ) : ℕ :=
  Nat.pair stateCode <|
    Nat.pair inputArity <|
      Nat.pair rowBase <|
        Nat.pair fieldLimit <|
          Nat.pair width <|
            Nat.pair rowIndex padding

/-- At padding zero the padded request is the published one. -/
theorem selectiveNodeRowPaddedInput_zero
    (stateCode inputArity rowBase fieldLimit width rowIndex : ℕ) :
    selectiveNodeRowPaddedInput stateCode inputArity rowBase fieldLimit width
        rowIndex 0 =
      selectiveNodeRowInput stateCode inputArity rowBase fieldLimit width
        rowIndex := rfl

set_option maxHeartbeats 1600000 in
-- Nineteen straight-line steps set up the loop's registers.
private theorem run_nodeRowPrologue {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (padding : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (entry : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveNodeRowPaddedInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val padding) ≤
        maximumBits)
    (hpc : entry.pc = 0)
    (hinput :
      entry.registers 0 =
        selectiveNodeRowPaddedInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val padding)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 19 →
      NodeRowFrame state row 0 5 (selectiveCountCasesSpineCode []) resumed →
      runNPOracleProgram selectiveNodeRowProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveNodeRowProgram maximumBits (19 + extraFuel)
        entry =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveNodeRowPaddedInput] at hflat
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
  have hzeroTagBits := natBitLength_pair_right hfive
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show (19 : ℕ) + extraFuel =
    extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveNodeRowProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveNodeRowPaddedInput]) hstateBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (descriptionWidth n bound) <|
        Nat.pair (row.val * rowWidth n bound) <|
          Nat.pair (boundedCircuitFieldLimit n bound) <|
            Nat.pair n (Nat.pair row.val padding))
    (selectiveNodeRowProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveNodeRowPaddedInput])
    hone]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveNodeRowProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveNodeRowProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveNodeRowProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveNodeRowProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairLeft_instruction (value := descriptionWidth n bound)
    (selectiveNodeRowProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound) <|
        Nat.pair (boundedCircuitFieldLimit n bound) <|
          Nat.pair n (Nat.pair row.val padding))
    (selectiveNodeRowProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [run_unpairLeft_instruction (value := row.val * rowWidth n bound)
    (selectiveNodeRowProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowBaseBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound) <|
        Nat.pair n (Nat.pair row.val padding))
    (selectiveNodeRowProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [run_unpairLeft_instruction (value := boundedCircuitFieldLimit n bound)
    (selectiveNodeRowProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair n (Nat.pair row.val padding))
    (selectiveNodeRowProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [run_unpairLeft_instruction (value := n)
    (selectiveNodeRowProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction (value := Nat.pair row.val padding)
    (selectiveNodeRowProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [run_unpairLeft_instruction (value := row.val)
    (selectiveNodeRowProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowIndexBits]
  rw [run_unpairRight_instruction (value := padding)
    (selectiveNodeRowProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hzeroTagBits]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 16) rfl) rfl
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 17) rfl) rfl
    (hsmall 5 (by omega))]
  rw [run_set_instruction
    (selectiveNodeRowProgram_controllerAt (pc := 18) rfl) rfl
    (hsmall 0 (by omega))]
  refine hcontinue _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump,
      selectiveCountCasesSpineCode]

/-- The wire the `k`-th grammar row case compiles. -/
private def nodeRowWire0 {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1)) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr state
    (selectiveGrammarCaseExpr (n := n) row row.val 0)

private def nodeRowWire1 {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1)) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr (nodeRowWire0 state row).state
    (selectiveGrammarCaseExpr (n := n) row row.val 1)

private def nodeRowWire2 {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1)) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr (nodeRowWire1 state row).state
    (selectiveGrammarCaseExpr (n := n) row row.val 2)

private def nodeRowWire3 {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1)) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr (nodeRowWire2 state row).state
    (selectiveGrammarCaseExpr (n := n) row row.val 3)

private def nodeRowWire4 {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1)) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr (nodeRowWire3 state row).state
    (selectiveGrammarCaseExpr (n := n) row row.val 4)

/-- The fold's constant base case. -/
private def nodeRowBaseWire {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1)) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveConst (nodeRowWire4 state row).state false

/-- The retained reverse spine at the loop exit. -/
private def nodeRowSpineValues {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) : List ℕ :=
  [(nodeRowWire4 state row).output, (nodeRowWire3 state row).output,
    (nodeRowWire2 state row).output, (nodeRowWire1 state row).output,
    (nodeRowWire0 state row).output]

/-- Interpreter fuel of one loop iteration. -/
private def nodeRowIterationFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag extraFuel : ℕ) : ℕ :=
  1 +
    (10 +
      (selectiveGrammarCaseRunFuel state row caseTag + (7 + (6 + extraFuel))))

/-- Register width of one loop iteration. -/
private def nodeRowIterationBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (row : Fin (bound + 1))
    (caseTag : ℕ) (values : List ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveGrammarCaseInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound)
        (boundedCircuitFieldLimit n bound) n row.val caseTag)) <|
    max (selectiveGrammarCaseRunBits state row caseTag) <|
      max
        (natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileExpr state
                (selectiveGrammarCaseExpr (n := n) row row.val caseTag))))) <|
        natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveCompileExpr state
              (selectiveGrammarCaseExpr (n := n) row row.val caseTag)).output ::
              values))

/-- Interpreter fuel of one whole node-row compilation. -/
def selectiveNodeRowRunFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) : ℕ :=
  19 +
    nodeRowIterationFuel state row 0
      (nodeRowIterationFuel (nodeRowWire0 state row).state row 1
        (nodeRowIterationFuel (nodeRowWire1 state row).state row 2
          (nodeRowIterationFuel (nodeRowWire2 state row).state row 3
            (nodeRowIterationFuel (nodeRowWire3 state row).state row 4
              (5 +
                (5 +
                  (selectiveEmitFuel
                      ((nodeRowWire4 state row).state.target -
                        (nodeRowWire4 state row).state.next)
                      (selectiveSelectedCode
                        (nodeRowWire4 state row).state.selected) +
                    (7 +
                      nodeRowFoldFuel (nodeRowBaseWire state row).state
                        (nodeRowBaseWire state row).output
                        (nodeRowSpineValues state row)))))))))

/-- Register width of one whole node-row compilation. -/
def selectiveNodeRowRunBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) : ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveNodeRowInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val)) <|
      max (nodeRowIterationBits state row 0 []) <|
        max
          (nodeRowIterationBits (nodeRowWire0 state row).state row 1
            [(nodeRowWire0 state row).output]) <|
          max
            (nodeRowIterationBits (nodeRowWire1 state row).state row 2
              [(nodeRowWire1 state row).output,
                (nodeRowWire0 state row).output]) <|
            max
              (nodeRowIterationBits (nodeRowWire2 state row).state row 3
                [(nodeRowWire2 state row).output,
                  (nodeRowWire1 state row).output,
                  (nodeRowWire0 state row).output]) <|
              max
                (nodeRowIterationBits (nodeRowWire3 state row).state row 4
                  [(nodeRowWire3 state row).output,
                    (nodeRowWire2 state row).output,
                    (nodeRowWire1 state row).output,
                    (nodeRowWire0 state row).output]) <|
                max
                  (natBitLength
                    (selectiveEmitInput
                      ((nodeRowWire4 state row).state.target -
                        (nodeRowWire4 state row).state.next)
                      (nodeRowWire4 state row).state.next
                      (selectiveSelectedCode
                        (nodeRowWire4 state row).state.selected)
                      (rawCircuitNodeCode (n := descriptionWidth n bound)
                        (.const false)))) <|
                  max
                    (natBitLength
                      (Nat.pair 0
                        (selectiveWireCode (nodeRowBaseWire state row)))) <|
                    nodeRowFoldBits (nodeRowBaseWire state row).state
                      (nodeRowBaseWire state row).output
                      (nodeRowSpineValues state row)

set_option maxHeartbeats 1600000 in
-- Nineteen parser steps, five loop iterations and the reverse fold.
/-- **The node-row compiler's run.**  The `534`-instruction stream started on
its own ABI frame, at any entry registers, returns exactly the compiler wire the
source compiler produces for the row's node-row predicate. -/
theorem run_selectiveNodeRowProgram {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (padding maximumBits : ℕ)
    (hordered : selectiveStateOrdered state)
    (hbits : selectiveNodeRowRunBits state row ≤ maximumBits)
    (hpaddedRequestBits :
      natBitLength
          (selectiveNodeRowPaddedInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val padding) ≤
        maximumBits)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveNodeRowPaddedInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val padding) :
    runNPOracleProgram selectiveNodeRowProgram maximumBits
        (selectiveNodeRowRunFuel state row) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state (nodeRowExpr (n := n) row))) := by
  unfold selectiveNodeRowRunBits at hbits
  have hsevenBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hiterZero := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hiterOne := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have hiterTwo := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hiterThree := (Nat.le_max_left _ _).trans hbitsFive
  have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
  have hiterFour := (Nat.le_max_left _ _).trans hbitsSix
  have hbitsSeven := (Nat.le_max_right _ _).trans hbitsSix
  have hemitInputBits := (Nat.le_max_left _ _).trans hbitsSeven
  have hbitsEight := (Nat.le_max_right _ _).trans hbitsSeven
  have hemitWireBits := (Nat.le_max_left _ _).trans hbitsEight
  have hfoldBits := (Nat.le_max_right _ _).trans hbitsEight
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have horderedZero : selectiveStateOrdered (nodeRowWire0 state row).state :=
    selectiveCompileExpr_ordered state _ hordered
  have horderedOne : selectiveStateOrdered (nodeRowWire1 state row).state :=
    selectiveCompileExpr_ordered _ _ horderedZero
  have horderedTwo : selectiveStateOrdered (nodeRowWire2 state row).state :=
    selectiveCompileExpr_ordered _ _ horderedOne
  have horderedThree : selectiveStateOrdered (nodeRowWire3 state row).state :=
    selectiveCompileExpr_ordered _ _ horderedTwo
  have horderedFour : selectiveStateOrdered (nodeRowWire4 state row).state :=
    selectiveCompileExpr_ordered _ _ horderedThree
  have hheads :
      selectiveUnaryHeads state (selectiveNodeRowExprs (n := n) row) =
        { state := (nodeRowWire4 state row).state
          values :=
            [(nodeRowWire0 state row).output, (nodeRowWire1 state row).output,
              (nodeRowWire2 state row).output, (nodeRowWire3 state row).output,
              (nodeRowWire4 state row).output] } := rfl
  rw [← boolExpr_any_selectiveNodeRowExprs row, selectiveCompileExpr_any_eq_fold,
    hheads]
  unfold selectiveNodeRowRunFuel
  refine run_nodeRowPrologue state row padding _ _ _ entry hsevenBits
    hpaddedRequestBits hentryPc hentryInput ?_
  intro afterPrologue hprologuePc hprologueFrame
  unfold nodeRowIterationFuel
  unfold nodeRowIterationBits at hiterZero
  refine run_nodeRowIteration state row 0 4 [] hordered _ _ _ _ afterPrologue
    rfl ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hiterZero))
    ((Nat.le_max_left _ _).trans hiterZero)
    ((Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterZero)))
    ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterZero)))
    (hsmall 1 (by omega)) (hsmall 4 (by omega)) (hsmall 0 (by omega))
    (hsmall 1 (by omega)) hprologuePc hprologueFrame ?_
  intro afterZero hzeroPc hzeroFrame
  unfold nodeRowIterationBits at hiterOne
  refine run_nodeRowIteration (nodeRowWire0 state row).state row 1 3
    [(nodeRowWire0 state row).output] horderedZero _ _ _ _ afterZero rfl
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hiterOne))
    ((Nat.le_max_left _ _).trans hiterOne)
    ((Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterOne)))
    ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterOne)))
    (hsmall 2 (by omega)) (hsmall 3 (by omega)) (hsmall 0 (by omega))
    (hsmall 1 (by omega)) hzeroPc hzeroFrame ?_
  intro afterOne honePc honeFrame
  unfold nodeRowIterationBits at hiterTwo
  refine run_nodeRowIteration (nodeRowWire1 state row).state row 2 2
    [(nodeRowWire1 state row).output, (nodeRowWire0 state row).output]
    horderedOne _ _ _ _ afterOne rfl
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hiterTwo))
    ((Nat.le_max_left _ _).trans hiterTwo)
    ((Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterTwo)))
    ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterTwo)))
    (hsmall 3 (by omega)) (hsmall 2 (by omega)) (hsmall 0 (by omega))
    (hsmall 1 (by omega)) honePc honeFrame ?_
  intro afterTwo htwoPc htwoFrame
  unfold nodeRowIterationBits at hiterThree
  refine run_nodeRowIteration (nodeRowWire2 state row).state row 3 1
    [(nodeRowWire2 state row).output, (nodeRowWire1 state row).output,
      (nodeRowWire0 state row).output] horderedTwo _ _ _ _ afterTwo rfl
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hiterThree))
    ((Nat.le_max_left _ _).trans hiterThree)
    ((Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterThree)))
    ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterThree)))
    (hsmall 4 (by omega)) (hsmall 1 (by omega)) (hsmall 0 (by omega))
    (hsmall 1 (by omega)) htwoPc htwoFrame ?_
  intro afterThree hthreePc hthreeFrame
  unfold nodeRowIterationBits at hiterFour
  refine run_nodeRowIteration (nodeRowWire3 state row).state row 4 0
    [(nodeRowWire3 state row).output, (nodeRowWire2 state row).output,
      (nodeRowWire1 state row).output, (nodeRowWire0 state row).output]
    horderedThree _ _ _ _ afterThree rfl
    ((Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hiterFour))
    ((Nat.le_max_left _ _).trans hiterFour)
    ((Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterFour)))
    ((Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hiterFour)))
    (hsmall 5 (by omega)) (hsmall 0 (by omega)) (hsmall 0 (by omega))
    (hsmall 1 (by omega)) hthreePc hthreeFrame ?_
  intro afterFour hfourPc hfourFrame
  refine run_nodeRowExit (nodeRowWire4 state row).state row 5 _ _ _ _
    afterFour (hsmall 0 (by omega)) hfourPc hfourFrame ?_
  intro afterExit hexitPc hexitNode hexitFrame
  refine run_nodeRowEmitCall (nodeRowWire4 state row).state (.const false) row 5
    0 _ horderedFour _ _ _ _ afterExit rfl hemitInputBits hemitWireBits
    (hsmall 0 (by omega)) hexitPc hexitNode hexitFrame ?_
  intro afterBase hbasePc hbaseWire hbaseOutput hbaseFrame
  exact run_nodeRowFoldLoop row 5 _ hsevenBits (nodeRowSpineValues state row)
    (nodeRowBaseWire state row).state (nodeRowBaseWire state row).output
    afterBase (selectiveState_emit_ordered _ _ horderedFour) hfoldBits hbasePc
    hbaseWire hbaseOutput hbaseFrame

/-- **Level premise, discharged.**  The node-row compiler compiles one
description row's node-row predicate at its own ABI frame, at an arbitrary entry
state, with resources depending on the request alone.  Nothing on this level is
left as a premise. -/
structure SelectiveNodeRowRunner (width bound : ℕ) where
  /-- Register width of one node-row compilation. -/
  bits : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) → ℕ
  /-- Interpreter fuel of one node-row compilation. -/
  fuel : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) → ℕ
  /-- The published run, at an arbitrary entry state. -/
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (row : Fin (bound + 1)), selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveNodeRowInput (selectiveStateCode state)
        (descriptionWidth width bound) (row.val * rowWidth width bound)
        (boundedCircuitFieldLimit width bound) width row.val →
    runNPOracleProgram selectiveNodeRowProgram (bits state row)
        (fuel state row) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state (nodeRowExpr (n := width) row)))

/-- The node-row level, discharged from `SelectiveGrammarCaseRun`'s closed
grammar-case run alone. -/
def selectiveNodeRowRunner (width bound : ℕ) :
    SelectiveNodeRowRunner width bound where
  bits state row := selectiveNodeRowRunBits state row
  fuel state row := selectiveNodeRowRunFuel state row
  executes := by
    intro state row hordered entry hentryPc hentryInput
    exact run_selectiveNodeRowProgram state row 0 _ hordered (le_refl _)
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) entry hentryPc
      hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
