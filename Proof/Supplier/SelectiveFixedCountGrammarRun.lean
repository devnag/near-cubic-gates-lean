import Proof.Supplier.SelectiveFixedCountRun
import Proof.Supplier.SelectiveNodeRowRun
import Batteries.Tactic.OpenPrivate

/-!
# The fixed-count grammar compiler's run

`selectiveFixedCountGrammarProgram` is the `1095`-instruction stream that
compiles one candidate node count's exact grammar predicate: a controller of
`97` instructions with three relocated callees, the `534`-instruction node-row
compiler, the `446`-instruction grammar-case compiler and the `18`-instruction
append transition.

The controller walks the description rows in order.  Register `30` names the
phase — `0` while the candidate's node rows are compiled, `1` for the single
output row, `2` for the padding rows — and the three-way dispatch at `63`–`69`
returns to whichever loop head the phase belongs to.  Both loops share one
physical return block at `51`, so the row cursor in registers `20` and `22`
advances exactly once per compiled row and every compiled output lands on one
private reverse spine in register `28`.  The exit emits the canonical `true`
base case and folds that spine back into the source compiler's right-associated
conjunction.

This module executes that controller, discharging
`SelectiveFixedCountRun.SelectiveFixedCountGrammarRunner` from the two closed
levels below it alone.
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
  selectiveNodeRowProgram selectiveNodeRowProgram_length
  selectiveFixedCountGrammarControllerProgram
  selectiveFixedCountGrammarControllerProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The row schedule, at the typed level

The controller's three phases are exactly the three segments of the source
compiler's conjunct list: one node row per candidate node, the output row, then
one padding row per remaining description row. -/

/-- The description rows the node-row phase visits. -/
private def fixedCountNodeRows {bound : ℕ} (candidate : Fin bound) :
    List (Fin (bound + 1)) :=
  List.ofFn fun index : Fin (candidate.val + 1) =>
    ⟨index.val, by
      have hcandidate := candidate.isLt
      have hindex := index.isLt
      omega⟩

/-- The description rows the padding phase visits. -/
private def fixedCountPaddingRows {bound : ℕ} (candidate : Fin bound) :
    List (Fin (bound + 1)) :=
  List.ofFn fun offset : Fin (bound - (candidate.val + 1)) =>
    ⟨candidate.val + 2 + offset.val, by
      have hcandidate := candidate.isLt
      have hoffset := offset.isLt
      omega⟩

/-- The single output row of one candidate. -/
private def grammarOutputRow {bound : ℕ} (candidate : Fin bound) :
    Fin (bound + 1) :=
  ⟨candidate.val + 1, by
    have hcandidate := candidate.isLt
    omega⟩

/-- The conjunct schedule the controller walks. -/
private def fixedCountGrammarExprs {n bound : ℕ} (candidate : Fin bound) :
    List (BoolExpr (descriptionWidth n bound)) :=
  countNodeRows (n := n) candidate ++
    outputRowExpr (n := n) (grammarOutputRow candidate) ::
      countPaddingRows (n := n) candidate

/-- **The controller's schedule, identified with the source compiler's exact
grammar predicate.** -/
private theorem boolExpr_all_fixedCountGrammarExprs {n bound : ℕ}
    (candidate : Fin bound) :
    BoolExpr.all (fixedCountGrammarExprs (n := n) candidate) =
      fixedCountGrammarExpr (n := n) candidate := rfl

private theorem countNodeRows_eq_map {n bound : ℕ} (candidate : Fin bound) :
    countNodeRows (n := n) candidate =
      (fixedCountNodeRows candidate).map (nodeRowExpr (n := n)) := by
  unfold countNodeRows fixedCountNodeRows
  rw [List.map_ofFn]
  rfl

private theorem countPaddingRows_eq_map {n bound : ℕ} (candidate : Fin bound) :
    countPaddingRows (n := n) candidate =
      (fixedCountPaddingRows candidate).map (paddingRowExpr (n := n)) := by
  unfold countPaddingRows fixedCountPaddingRows
  rw [List.map_ofFn]
  rfl

private theorem fixedCountNodeRows_length {bound : ℕ} (candidate : Fin bound) :
    (fixedCountNodeRows candidate).length = candidate.val + 1 := by
  simp [fixedCountNodeRows]

private theorem fixedCountPaddingRows_length {bound : ℕ}
    (candidate : Fin bound) :
    (fixedCountPaddingRows candidate).length = bound - (candidate.val + 1) := by
  simp [fixedCountPaddingRows]

/-- The row schedule a loop head walks: consecutive description rows from one
starting index.  Both loops of this controller enumerate exactly such a
segment, and the loop invariant needs nothing else about the rows. -/
private inductive GrammarRowsFrom (bound : ℕ) :
    ℕ → List (Fin (bound + 1)) → Prop
  | nil (rowIndex : ℕ) : GrammarRowsFrom bound rowIndex []
  | cons {rowIndex : ℕ} {row : Fin (bound + 1)}
      {rest : List (Fin (bound + 1))} (hhead : row.val = rowIndex)
      (hrest : GrammarRowsFrom bound (rowIndex + 1) rest) :
      GrammarRowsFrom bound rowIndex (row :: rest)

private theorem grammarRowsFrom_ofFn (bound : ℕ) :
    ∀ (count start : ℕ) (rows : Fin count → Fin (bound + 1)),
      (∀ position : Fin count, (rows position).val = start + position.val) →
      GrammarRowsFrom bound start (List.ofFn rows)
  | 0, start, _, _ => by
      simpa using GrammarRowsFrom.nil (bound := bound) start
  | count + 1, start, rows, hrows => by
      rw [List.ofFn_succ]
      refine GrammarRowsFrom.cons (by rw [hrows 0]; simp) ?_
      refine grammarRowsFrom_ofFn bound count (start + 1)
        (fun position => rows position.succ) ?_
      intro position
      have hposition := hrows position.succ
      simp only [Fin.val_succ] at hposition
      omega

private theorem grammarRowsFrom_nodeRows {bound : ℕ} (candidate : Fin bound) :
    GrammarRowsFrom bound 0 (fixedCountNodeRows candidate) := by
  refine grammarRowsFrom_ofFn bound (candidate.val + 1) 0 _ ?_
  intro position
  simp

private theorem grammarRowsFrom_paddingRows {bound : ℕ}
    (candidate : Fin bound) :
    GrammarRowsFrom bound (candidate.val + 2)
      (fixedCountPaddingRows candidate) := by
  refine grammarRowsFrom_ofFn bound (bound - (candidate.val + 1))
    (candidate.val + 2) _ ?_
  intro position
  rfl

/-- The forward pass, in the order the controller accumulates it: the compiler
state it reaches and the reverse spine it retains. -/
private def grammarPass {n : ℕ} :
    SelectiveState n → List (BoolExpr n) → List ℕ →
      SelectiveState n × List ℕ
  | state, [], values => (state, values)
  | state, expression :: rest, values =>
      grammarPass (selectiveCompileExpr state expression).state rest
        ((selectiveCompileExpr state expression).output :: values)

private theorem grammarPass_eq {n : ℕ} :
    ∀ (expressions : List (BoolExpr n)) (state : SelectiveState n)
      (values : List ℕ),
      grammarPass state expressions values =
        ((selectiveUnaryHeads state expressions).state,
          (selectiveUnaryHeads state expressions).values.reverse ++ values)
  | [], state, values => by
      simp [grammarPass, selectiveUnaryHeads]
  | expression :: rest, state, values => by
      simp only [grammarPass, selectiveUnaryHeads,
        grammarPass_eq rest _ _, List.reverse_cons, List.append_assoc,
        List.singleton_append]

private theorem grammarPass_append {n : ℕ} :
    ∀ (first second : List (BoolExpr n)) (state : SelectiveState n)
      (values : List ℕ),
      grammarPass state (first ++ second) values =
        grammarPass (grammarPass state first values).1 second
          (grammarPass state first values).2
  | [], _, _, _ => rfl
  | expression :: rest, second, state, values => by
      simp only [List.cons_append, grammarPass]
      exact grammarPass_append rest second _ _

private theorem grammarPass_ordered {n : ℕ} :
    ∀ (expressions : List (BoolExpr n)) (state : SelectiveState n)
      (values : List ℕ), selectiveStateOrdered state →
      selectiveStateOrdered (grammarPass state expressions values).1
  | [], _, _, hordered => hordered
  | expression :: rest, state, _, hordered =>
      grammarPass_ordered rest _ _
        (selectiveCompileExpr_ordered state expression hordered)

/-! ## 2. Decoding the fixed 1095-instruction stream

The controller occupies the first `97` positions, the node-row compiler the
next `534`, the grammar-case compiler the next `446` and the append callee the
last `18`. -/

private theorem selectiveFixedCountGrammarProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveFixedCountGrammarControllerProgram 97 631 1077)[pc]? =
        some instruction) :
    selectiveFixedCountGrammarProgram[pc]? = some instruction := by
  have hpc :
      pc < (selectiveFixedCountGrammarControllerProgram 97 631 1077).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveFixedCountGrammarControllerProgram_length] at hpc
  simp only [selectiveFixedCountGrammarProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length, selectiveGrammarCaseProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveFixedCountGrammarControllerProgram_length]
    omega)]
  exact hlookup

private theorem selectiveFixedCountGrammarProgram_nodeRowCallable :
    ProgramCallableAt selectiveFixedCountGrammarProgram selectiveNodeRowProgram
      97 1000 50 51 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveNodeRowProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveNodeRowProgram_length] at hpc
  simp only [selectiveFixedCountGrammarProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length, selectiveGrammarCaseProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveFixedCountGrammarControllerProgram_length]
    omega)]
  simp only [selectiveFixedCountGrammarControllerProgram_length]
  rw [show 97 + pc - 97 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveFixedCountGrammarProgram_caseCallable :
    ProgramCallableAt selectiveFixedCountGrammarProgram
      selectiveGrammarCaseProgram 631 15000 50 51 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveGrammarCaseProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveGrammarCaseProgram_length] at hpc
  simp only [selectiveFixedCountGrammarProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length, selectiveGrammarCaseProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveFixedCountGrammarControllerProgram_length,
    selectiveNodeRowProgram_length]
  rw [show 631 + pc - (97 + 534) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveFixedCountGrammarProgram_emitCallable :
    ProgramCallableAt selectiveFixedCountGrammarProgram selectiveEmitProgram
      1077 26000 50 79 := by
  intro pc instruction hlookup
  simp only [selectiveFixedCountGrammarProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveFixedCountGrammarControllerProgram_length,
      selectiveNodeRowProgram_length, selectiveGrammarCaseProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveFixedCountGrammarControllerProgram_length,
    selectiveNodeRowProgram_length, selectiveGrammarCaseProgram_length]
  rw [show 1077 + pc - (97 + 534 + 446) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The controller's live frame and its three call blocks

Both loop heads, the shared return block and the reverse fold read one live
register frame: the compiler state, the four request constants, the row cursor,
the two countdowns and the retained spine.  Register `29` is the controller's
branch register; nothing writes it, and the frame carries its entry value so
that the coincident-target branches stay coincident. -/

private theorem jump_registers_eq (machine : NPOracleState)
    (target index : ℕ) :
    (machine.jump target).registers index = machine.registers index := rfl

/-- The controller's live register frame. -/
private def GrammarFrame {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (branch rowIndex nodeRemaining padRemaining spine : ℕ)
    (machine : NPOracleState) : Prop :=
  machine.registers 4 = state.target - state.next ∧
    machine.registers 6 = state.next ∧
      machine.registers 7 = selectiveSelectedCode state.selected ∧
        machine.registers 8 = descriptionWidth n bound ∧
          machine.registers 10 = rowWidth n bound ∧
            machine.registers 12 = boundedCircuitFieldLimit n bound ∧
              machine.registers 14 = n ∧
                machine.registers 20 = rowIndex ∧
                  machine.registers 22 = rowIndex * rowWidth n bound ∧
                    machine.registers 24 = nodeRemaining ∧
                      machine.registers 26 = padRemaining ∧
                        machine.registers 28 = spine ∧
                          machine.registers 29 = branch

set_option maxHeartbeats 1600000 in
-- Eleven request steps around the relocated node-row compiler.
private theorem run_grammarNodeCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (branch rowIndex nodeRemaining padRemaining spine : ℕ)
    (hordered : selectiveStateOrdered state) (hrowIndex : row.val = rowIndex)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeFuel : calleeFuel = selectiveNodeRowRunFuel state row)
    (hcalleeBits : selectiveNodeRowRunBits state row ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveNodeRowInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileExpr state (nodeRowExpr (n := n) row)))) ≤
        maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (hpc : machine.pc = 23)
    (hframe :
      GrammarFrame state branch rowIndex nodeRemaining padRemaining spine
        machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 51 →
      resumed.registers 50 =
        Nat.pair 0
          (selectiveWireCode
            (selectiveCompileExpr state (nodeRowExpr (n := n) row))) →
      resumed.registers 30 = 0 →
      GrammarFrame state branch rowIndex nodeRemaining padRemaining spine
        resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (11 + (calleeFuel + extraFuel)) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth,
    hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveNodeRowInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n row.val =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (descriptionWidth n bound)
            (Nat.pair (row.val * rowWidth n bound)
              (Nat.pair (boundedCircuitFieldLimit n bound)
                (Nat.pair n (Nat.pair row.val 0))))) := rfl
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
  rw [show 11 + (calleeFuel + extraFuel) =
    (calleeFuel + extraFuel) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by
    omega]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 23) rfl) hpc
    hzeroBits]
  rw [run_pair_instruction (value := Nat.pair row.val 0)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 24) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hrowIndexReg, hrowIndex])
    hfive]
  rw [run_pair_instruction (value := Nat.pair n (Nat.pair row.val 0))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 25) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfour]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound)
        (Nat.pair n (Nat.pair row.val 0)))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 26) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hthree]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair (boundedCircuitFieldLimit n bound)
          (Nat.pair n (Nat.pair row.val 0))))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 27) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hrowBase, hrowIndex])
    htwo]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair (boundedCircuitFieldLimit n bound)
            (Nat.pair n (Nat.pair row.val 0)))))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 28) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 29) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 30) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveNodeRowInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound)
        (boundedCircuitFieldLimit n bound) n row.val)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 31) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 32) rfl) rfl
    hzeroBits]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 33) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveNodeRowProgram)
    (calleeOutput :=
      selectiveWireCode (selectiveCompileExpr state (nodeRowExpr (n := n) row)))
    selectiveFixedCountGrammarProgram_nodeRowCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_selectiveNodeRowProgram state row 0 maximumBits hordered
      hcalleeBits hrequestBits frame hframePc ?_
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump,
      selectiveNodeRowPaddedInput_zero]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _nodeHalt
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, hremaining,
        hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth, hrowIndexReg,
        hrowBase, hnodeCount, hpadCount, hspine, hbranch]

set_option maxHeartbeats 1600000 in
-- Ten request steps around the relocated grammar-case compiler.
private theorem run_grammarCaseCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (branch rowIndex nodeRemaining padRemaining spine caseTag phase : ℕ)
    (hordered : selectiveStateOrdered state) (hrowIndex : row.val = rowIndex)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeFuel : calleeFuel = selectiveGrammarCaseRunFuel state row caseTag)
    (hcalleeBits : selectiveGrammarCaseRunBits state row caseTag ≤ maximumBits)
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
    (hpc : machine.pc = 41)
    (hcaseTag : machine.registers 32 = caseTag)
    (hphase : machine.registers 30 = phase)
    (hframe :
      GrammarFrame state branch rowIndex nodeRemaining padRemaining spine
        machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 51 →
      resumed.registers 50 =
        Nat.pair 0
          (selectiveWireCode
            (selectiveCompileExpr state
              (selectiveGrammarCaseExpr (n := n) row row.val caseTag))) →
      resumed.registers 30 = phase →
      GrammarFrame state branch rowIndex nodeRemaining padRemaining spine
        resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (10 + (calleeFuel + extraFuel)) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth,
    hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩ := hframe
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
  rw [show 10 + (calleeFuel + extraFuel) =
    (calleeFuel + extraFuel) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair row.val caseTag)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 41) rfl) hpc
    (by rw [hrowIndexReg, hcaseTag, hrowIndex]) hfive]
  rw [run_pair_instruction (value := Nat.pair n (Nat.pair row.val caseTag))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 42) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfour]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound)
        (Nat.pair n (Nat.pair row.val caseTag)))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hthree]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair (boundedCircuitFieldLimit n bound)
          (Nat.pair n (Nat.pair row.val caseTag))))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 44) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase, hrowIndex])
    htwo]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair (boundedCircuitFieldLimit n bound)
            (Nat.pair n (Nat.pair row.val caseTag)))))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hone]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 46) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 47) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveGrammarCaseInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound)
        (boundedCircuitFieldLimit n bound) n row.val caseTag)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 48) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 49) rfl) rfl
    hzeroBits]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 50) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveGrammarCaseProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileExpr state
          (selectiveGrammarCaseExpr (n := n) row row.val caseTag)))
    selectiveFixedCountGrammarProgram_caseCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump, relocateState, hphase])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, hremaining,
        hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth, hrowIndexReg,
        hrowBase, hnodeCount, hpadCount, hspine, hbranch]

set_option maxHeartbeats 1600000 in
-- Seven unpacking steps, three spine steps and the two cursor steps: the one
-- physical return block both callees share.
private theorem run_grammarReturn {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (wire : SelectiveWire (descriptionWidth n bound))
    (branch rowIndex nodeRemaining padRemaining phase : ℕ) (values : List ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hwireBits :
      natBitLength (Nat.pair 0 (selectiveWireCode wire)) ≤ maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode (wire.output :: values)) ≤
        maximumBits)
    (hcursorBits :
      natBitLength ((rowIndex + 1) * rowWidth n bound) ≤ maximumBits)
    (hrowIndexBits : natBitLength (rowIndex + 1) ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hpc : machine.pc = 51)
    (haccumulator :
      machine.registers 50 = Nat.pair 0 (selectiveWireCode wire))
    (hphase : machine.registers 30 = phase)
    (hframe :
      GrammarFrame state branch rowIndex nodeRemaining padRemaining
        (selectiveCountCasesSpineCode values) machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 63 →
      resumed.registers 30 = phase →
      GrammarFrame wire.state branch (rowIndex + 1) nodeRemaining padRemaining
        (selectiveCountCasesSpineCode (wire.output :: values)) resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (12 + extraFuel) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth,
    hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth n bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
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
  have hspineForm :
      selectiveCountCasesSpineCode (wire.output :: values) =
        Nat.pair 1
          (Nat.pair wire.output (selectiveCountCasesSpineCode values)) := rfl
  have hconsBits :
      natBitLength
          (Nat.pair wire.output (selectiveCountCasesSpineCode values)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  rw [show 12 + extraFuel =
    extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveWireCode wire)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 51) rfl) hpc
    (by rw [haccumulator]; simp) hwireFlat]
  rw [run_unpairLeft_instruction (value := selectiveStateCode wire.state)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 52) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
    hcompiledStateBits]
  rw [run_unpairRight_instruction (value := wire.output)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 53) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
    hcompiledOutputBits]
  rw [run_unpairLeft_instruction
    (value := wire.state.target - wire.state.next)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 54) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hcompiledRemainingBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair wire.state.next (selectiveSelectedCode wire.state.selected))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 55) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hcompiledTailBits]
  rw [run_unpairLeft_instruction (value := wire.state.next)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 56) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode wire.state.selected)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 57) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledSelectedBits]
  rw [run_pair_instruction
    (value := Nat.pair wire.output (selectiveCountCasesSpineCode values))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 58) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hspine]) hconsBits]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 59) rfl) rfl
    honeBits]
  rw [run_pair_instruction
    (value := selectiveCountCasesSpineCode (wire.output :: values))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 60) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hspineForm]) hspineBits]
  rw [run_add_instruction (value := (rowIndex + 1) * rowWidth n bound)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 61) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hrowBase, hrowWidth,
        add_one_mul])
    hcursorBits]
  rw [run_increment_instruction (value := rowIndex + 1)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 62) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowIndexReg])
    hrowIndexBits]
  refine hcontinue _ rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hphase])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, harity, hrowWidth,
      hfieldLimit, hwidth, hnodeCount, hpadCount, hbranch]

/-! ## 4. The three phases

Every compiled row leaves the shared return block at `63` with the phase still
in register `30`, and the saturating dispatch there sends it back to its own
loop head. -/

/-- Interpreter fuel of the node-row loop from the head at `22`. -/
private def grammarNodeLoopFuel {n bound : ℕ} :
    SelectiveState (descriptionWidth n bound) → List (Fin (bound + 1)) → ℕ →
      ℕ
  | _, [], extraFuel => 1 + extraFuel
  | state, row :: rest, extraFuel =>
      1 +
        (11 +
          (selectiveNodeRowRunFuel state row +
            (12 +
              (3 +
                grammarNodeLoopFuel
                  (selectiveCompileExpr state (nodeRowExpr (n := n) row)).state
                  rest extraFuel))))

/-- Register width of the node-row loop from the head at `22`. -/
private def grammarNodeLoopBits {n bound : ℕ} :
    SelectiveState (descriptionWidth n bound) → List (Fin (bound + 1)) →
      List ℕ → ℕ
  | _, [], _ => 0
  | state, row :: rest, values =>
      max
        (natBitLength
          (selectiveNodeRowInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val)) <|
        max (selectiveNodeRowRunBits state row) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveCompileExpr state (nodeRowExpr (n := n) row))))) <|
            max
              (natBitLength
                (selectiveCountCasesSpineCode
                  ((selectiveCompileExpr state
                    (nodeRowExpr (n := n) row)).output :: values))) <|
              max (natBitLength ((row.val + 1) * rowWidth n bound)) <|
                max (natBitLength (row.val + 1)) <|
                  max (natBitLength rest.length) <|
                    grammarNodeLoopBits
                      (selectiveCompileExpr state
                        (nodeRowExpr (n := n) row)).state rest
                      ((selectiveCompileExpr state
                        (nodeRowExpr (n := n) row)).output :: values)

set_option maxHeartbeats 3200000 in
-- The node-row phase is one induction on the rows it still has to compile.
private theorem run_grammarNodeLoop {n bound : ℕ}
    (branch padRemaining maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (rows : List (Fin (bound + 1))) (rowIndex : ℕ)
      (state : SelectiveState (descriptionWidth n bound)) (values : List ℕ)
      (machine : NPOracleState) (extraFuel finalOutput : ℕ),
      GrammarRowsFrom bound rowIndex rows →
      selectiveStateOrdered state →
      grammarNodeLoopBits state rows values ≤ maximumBits →
      machine.pc = 22 →
      GrammarFrame state branch rowIndex rows.length padRemaining
        (selectiveCountCasesSpineCode values) machine →
      (∀ resumed : NPOracleState, resumed.pc = 34 →
        GrammarFrame
          (grammarPass state (rows.map (nodeRowExpr (n := n))) values).1 branch
          (rowIndex + rows.length) 0 padRemaining
          (selectiveCountCasesSpineCode
            (grammarPass state (rows.map (nodeRowExpr (n := n)))
              values).2) resumed →
        runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
            extraFuel resumed =
          some finalOutput) →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          (grammarNodeLoopFuel state rows extraFuel) machine =
        some finalOutput := by
  intro rows
  induction rows with
  | nil =>
      intro rowIndex state values machine extraFuel finalOutput _ _ _ hpc
        hframe hcontinue
      have hcount := hframe.2.2.2.2.2.2.2.2.2.1
      simp only [grammarNodeLoopFuel]
      rw [show 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 22) rfl) hpc]
      rw [if_pos (by rw [hcount]; rfl)]
      refine hcontinue _ rfl ?_
      simp only [List.map_nil, grammarPass, List.length_nil, Nat.add_zero]
      obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
        hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
        hbranch⟩ := hframe
      exact ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
        hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩
  | cons row rest inductionHypothesis =>
      intro rowIndex state values machine extraFuel finalOutput hschedule
        hordered hbits hpc hframe hcontinue
      have hcount := hframe.2.2.2.2.2.2.2.2.2.1
      cases hschedule with
      | cons hhead hrest =>
        simp only [grammarNodeLoopBits] at hbits
        have hrequestBits := (Nat.le_max_left _ _).trans hbits
        have hbitsOne := (Nat.le_max_right _ _).trans hbits
        have hcalleeBits := (Nat.le_max_left _ _).trans hbitsOne
        have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
        have hwireBits := (Nat.le_max_left _ _).trans hbitsTwo
        have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
        have hspineBits := (Nat.le_max_left _ _).trans hbitsThree
        have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
        have hcursorBits := (Nat.le_max_left _ _).trans hbitsFour
        have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
        have hrowIndexBits := (Nat.le_max_left _ _).trans hbitsFive
        have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
        have hlengthBits := (Nat.le_max_left _ _).trans hbitsSix
        have hrecursiveBits := (Nat.le_max_right _ _).trans hbitsSix
        have hsmall : ∀ value : ℕ, value ≤ 7 →
            natBitLength value ≤ maximumBits :=
          fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
        simp only [grammarNodeLoopFuel]
        rw [show 1 +
            (11 +
              (selectiveNodeRowRunFuel state row +
                (12 +
                  (3 +
                    grammarNodeLoopFuel
                      (selectiveCompileExpr state
                        (nodeRowExpr (n := n) row)).state rest extraFuel)))) =
          (11 +
            (selectiveNodeRowRunFuel state row +
              (12 +
                (3 +
                  grammarNodeLoopFuel
                    (selectiveCompileExpr state
                      (nodeRowExpr (n := n) row)).state rest extraFuel)))) +
            1 by omega]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 22) rfl) hpc]
        rw [if_neg (by rw [hcount]; simp)]
        refine run_grammarNodeCall state row branch rowIndex
          (rest.length + 1) padRemaining (selectiveCountCasesSpineCode values)
          hordered hhead maximumBits _ _ _ _ rfl hcalleeBits hrequestBits
          hwireBits (hsmall 0 (by omega)) rfl ?_ ?_
        · obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
            hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
            hbranch⟩ := hframe
          exact ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
            hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
            hbranch⟩
        intro middle hmiddlePc hmiddleAccumulator hmiddlePhase hmiddleFrame
        refine run_grammarReturn state
          (selectiveCompileExpr state (nodeRowExpr (n := n) row)) branch
          rowIndex (rest.length + 1) padRemaining 0 values maximumBits _ _
          middle hwireBits hspineBits (by rw [← hhead]; exact hcursorBits)
          (by rw [← hhead]; exact hrowIndexBits) (hsmall 1 (by omega))
          hmiddlePc hmiddleAccumulator hmiddlePhase hmiddleFrame ?_
        intro resumed hresumedPc hresumedPhase hresumedFrame
        obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
          hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
          hbranch⟩ := hresumedFrame
        rw [show (3 : ℕ) + grammarNodeLoopFuel
            (selectiveCompileExpr state (nodeRowExpr (n := n) row)).state rest
            extraFuel =
          grammarNodeLoopFuel
            (selectiveCompileExpr state (nodeRowExpr (n := n) row)).state rest
            extraFuel + 1 + 1 + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 63) rfl)
          hresumedPc]
        rw [if_pos hresumedPhase]
        rw [run_decrement_instruction (value := rest.length)
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 64) rfl) rfl
          (by simp [NPOracleState.jump, hnodeCount])
          hlengthBits]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 65) rfl) rfl]
        simp only [ite_self]
        have hcontinueRest :
            ∀ final : NPOracleState, final.pc = 34 →
              GrammarFrame
                (grammarPass
                  (selectiveCompileExpr state (nodeRowExpr (n := n) row)).state
                  (rest.map (nodeRowExpr (n := n)))
                  ((selectiveCompileExpr state
                    (nodeRowExpr (n := n) row)).output :: values)).1 branch
                (rowIndex + 1 + rest.length) 0 padRemaining
                (selectiveCountCasesSpineCode
                  (grammarPass
                    (selectiveCompileExpr state
                      (nodeRowExpr (n := n) row)).state
                    (rest.map (nodeRowExpr (n := n)))
                    ((selectiveCompileExpr state
                      (nodeRowExpr (n := n) row)).output :: values)).2)
                final →
              runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
                  extraFuel final =
                some finalOutput := by
          intro final hfinalPc hfinalFrame
          refine hcontinue final hfinalPc ?_
          simp only [List.map_cons, grammarPass, List.length_cons]
          rw [show rowIndex + (rest.length + 1) = rowIndex + 1 + rest.length by
            omega]
          exact hfinalFrame
        refine inductionHypothesis (rowIndex + 1)
          (selectiveCompileExpr state (nodeRowExpr (n := n) row)).state
          ((selectiveCompileExpr state (nodeRowExpr (n := n) row)).output ::
            values) _ extraFuel finalOutput hrest
          (selectiveCompileExpr_ordered state _ hordered) hrecursiveBits rfl
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcontinueRest <;>
          simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext,
            hselected, harity, hrowWidth, hfieldLimit, hwidth, hrowIndexReg,
            hrowBase, hpadCount, hspine, hbranch]

/-- Interpreter fuel of the padding loop from the head at `37`. -/
private def grammarPaddingLoopFuel {n bound : ℕ} :
    SelectiveState (descriptionWidth n bound) → List (Fin (bound + 1)) → ℕ →
      ℕ
  | _, [], extraFuel => 1 + extraFuel
  | state, row :: rest, extraFuel =>
      1 +
        (3 +
          (10 +
            (selectiveGrammarCaseRunFuel state row 6 +
              (12 +
                (5 +
                  grammarPaddingLoopFuel
                    (selectiveCompileExpr state
                      (paddingRowExpr (n := n) row)).state rest extraFuel)))))

/-- Register width of the padding loop from the head at `37`. -/
private def grammarPaddingLoopBits {n bound : ℕ} :
    SelectiveState (descriptionWidth n bound) → List (Fin (bound + 1)) →
      List ℕ → ℕ
  | _, [], _ => 0
  | state, row :: rest, values =>
      max
        (natBitLength
          (selectiveGrammarCaseInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n row.val 6)) <|
        max (selectiveGrammarCaseRunBits state row 6) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveCompileExpr state
                    (paddingRowExpr (n := n) row))))) <|
            max
              (natBitLength
                (selectiveCountCasesSpineCode
                  ((selectiveCompileExpr state
                    (paddingRowExpr (n := n) row)).output :: values))) <|
              max (natBitLength ((row.val + 1) * rowWidth n bound)) <|
                max (natBitLength (row.val + 1)) <|
                  max (natBitLength rest.length) <|
                    grammarPaddingLoopBits
                      (selectiveCompileExpr state
                        (paddingRowExpr (n := n) row)).state rest
                      ((selectiveCompileExpr state
                        (paddingRowExpr (n := n) row)).output :: values)

set_option maxHeartbeats 3200000 in
-- The padding phase is one induction on the rows it still has to compile.
private theorem run_grammarPaddingLoop {n bound : ℕ}
    (branch nodeRemaining maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (rows : List (Fin (bound + 1))) (rowIndex : ℕ)
      (state : SelectiveState (descriptionWidth n bound)) (values : List ℕ)
      (machine : NPOracleState) (extraFuel finalOutput : ℕ),
      GrammarRowsFrom bound rowIndex rows →
      selectiveStateOrdered state →
      grammarPaddingLoopBits state rows values ≤ maximumBits →
      machine.pc = 37 →
      GrammarFrame state branch rowIndex nodeRemaining rows.length
        (selectiveCountCasesSpineCode values) machine →
      (∀ resumed : NPOracleState, resumed.pc = 70 →
        GrammarFrame
          (grammarPass state (rows.map (paddingRowExpr (n := n))) values).1
          branch (rowIndex + rows.length) nodeRemaining 0
          (selectiveCountCasesSpineCode
            (grammarPass state (rows.map (paddingRowExpr (n := n)))
              values).2) resumed →
        runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
            extraFuel resumed =
          some finalOutput) →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          (grammarPaddingLoopFuel state rows extraFuel) machine =
        some finalOutput := by
  intro rows
  induction rows with
  | nil =>
      intro rowIndex state values machine extraFuel finalOutput _ _ _ hpc
        hframe hcontinue
      have hcount := hframe.2.2.2.2.2.2.2.2.2.2.1
      simp only [grammarPaddingLoopFuel]
      rw [show 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 37) rfl) hpc]
      rw [if_pos (by rw [hcount]; rfl)]
      refine hcontinue _ rfl ?_
      simp only [List.map_nil, grammarPass, List.length_nil, Nat.add_zero]
      obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
        hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
        hbranch⟩ := hframe
      exact ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
        hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩
  | cons row rest inductionHypothesis =>
      intro rowIndex state values machine extraFuel finalOutput hschedule
        hordered hbits hpc hframe hcontinue
      have hcount := hframe.2.2.2.2.2.2.2.2.2.2.1
      cases hschedule with
      | cons hhead hrest =>
        simp only [grammarPaddingLoopBits] at hbits
        have hrequestBits := (Nat.le_max_left _ _).trans hbits
        have hbitsOne := (Nat.le_max_right _ _).trans hbits
        have hcalleeBits := (Nat.le_max_left _ _).trans hbitsOne
        have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
        have hwireBits := (Nat.le_max_left _ _).trans hbitsTwo
        have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
        have hspineBits := (Nat.le_max_left _ _).trans hbitsThree
        have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
        have hcursorBits := (Nat.le_max_left _ _).trans hbitsFour
        have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
        have hrowIndexBits := (Nat.le_max_left _ _).trans hbitsFive
        have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
        have hlengthBits := (Nat.le_max_left _ _).trans hbitsSix
        have hrecursiveBits := (Nat.le_max_right _ _).trans hbitsSix
        have hsmall : ∀ value : ℕ, value ≤ 7 →
            natBitLength value ≤ maximumBits :=
          fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
        have hcase : selectiveGrammarCaseExpr (n := n) row row.val 6 =
            paddingRowExpr (n := n) row := selectiveGrammarCaseExpr_six row
        obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
          hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
          hbranch⟩ := hframe
        simp only [grammarPaddingLoopFuel]
        rw [show 1 +
            (3 +
              (10 +
                (selectiveGrammarCaseRunFuel state row 6 +
                  (12 +
                    (5 +
                      grammarPaddingLoopFuel
                        (selectiveCompileExpr state
                          (paddingRowExpr (n := n) row)).state rest
                        extraFuel))))) =
          (10 +
            (selectiveGrammarCaseRunFuel state row 6 +
              (12 +
                (5 +
                  grammarPaddingLoopFuel
                    (selectiveCompileExpr state
                      (paddingRowExpr (n := n) row)).state rest extraFuel)))) +
            1 + 1 + 1 + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 37) rfl) hpc]
        rw [if_neg (by rw [hcount]; simp)]
        rw [run_set_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 38) rfl) rfl
          (hsmall 6 (by omega))]
        rw [run_set_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 39) rfl) rfl
          (hsmall 2 (by omega))]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 40) rfl) rfl]
        simp only [ite_self]
        refine run_grammarCaseCall state row branch rowIndex nodeRemaining
          (rest.length + 1) (selectiveCountCasesSpineCode values) 6 2 hordered
          hhead maximumBits _ _ _ _ rfl hcalleeBits hrequestBits
          (by rw [hcase]; exact hwireBits) (hsmall 0 (by omega)) rfl
          (by simp [NPOracleState.write, NPOracleState.jump])
          (by simp [NPOracleState.write, NPOracleState.jump])
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
          try simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext,
            hselected, harity, hrowWidth, hfieldLimit, hwidth, hrowIndexReg,
            hrowBase, hnodeCount, hpadCount, hspine, hbranch]
        intro middle hmiddlePc hmiddleAccumulator hmiddlePhase hmiddleFrame
        rw [hcase] at hmiddleAccumulator
        refine run_grammarReturn state
          (selectiveCompileExpr state (paddingRowExpr (n := n) row)) branch
          rowIndex nodeRemaining (rest.length + 1) 2 values maximumBits _ _
          middle hwireBits hspineBits (by rw [← hhead]; exact hcursorBits)
          (by rw [← hhead]; exact hrowIndexBits) (hsmall 1 (by omega))
          hmiddlePc hmiddleAccumulator hmiddlePhase hmiddleFrame ?_
        intro resumed hresumedPc hresumedPhase hresumedFrame
        obtain ⟨hremainingTwo, hnextTwo, hselectedTwo, harityTwo, hrowWidthTwo,
          hfieldLimitTwo, hwidthTwo, hrowIndexRegTwo, hrowBaseTwo, hnodeCountTwo,
          hpadCountTwo, hspineTwo, hbranchTwo⟩ := hresumedFrame
        rw [show (5 : ℕ) + grammarPaddingLoopFuel
            (selectiveCompileExpr state (paddingRowExpr (n := n) row)).state
            rest extraFuel =
          grammarPaddingLoopFuel
            (selectiveCompileExpr state (paddingRowExpr (n := n) row)).state
            rest extraFuel + 1 + 1 + 1 + 1 + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 63) rfl)
          hresumedPc]
        rw [if_neg (by rw [hresumedPhase]; omega)]
        rw [run_decrement_instruction (value := 1)
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 66) rfl) rfl
          (by simp [NPOracleState.jump, hresumedPhase])
          (hsmall 1 (by omega))]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 67) rfl) rfl]
        rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [run_decrement_instruction (value := rest.length)
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 68) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, hpadCountTwo])
          hlengthBits]
        rw [run_branchZero_instruction
          (selectiveFixedCountGrammarProgram_controllerAt (pc := 69) rfl) rfl]
        simp only [ite_self]
        have hcontinueRest :
            ∀ final : NPOracleState, final.pc = 70 →
              GrammarFrame
                (grammarPass
                  (selectiveCompileExpr state
                    (paddingRowExpr (n := n) row)).state
                  (rest.map (paddingRowExpr (n := n)))
                  ((selectiveCompileExpr state
                    (paddingRowExpr (n := n) row)).output :: values)).1 branch
                (rowIndex + 1 + rest.length) nodeRemaining 0
                (selectiveCountCasesSpineCode
                  (grammarPass
                    (selectiveCompileExpr state
                      (paddingRowExpr (n := n) row)).state
                    (rest.map (paddingRowExpr (n := n)))
                    ((selectiveCompileExpr state
                      (paddingRowExpr (n := n) row)).output :: values)).2)
                final →
              runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
                  extraFuel final =
                some finalOutput := by
          intro final hfinalPc hfinalFrame
          refine hcontinue final hfinalPc ?_
          simp only [List.map_cons, grammarPass, List.length_cons]
          rw [show rowIndex + (rest.length + 1) = rowIndex + 1 + rest.length by
            omega]
          exact hfinalFrame
        refine inductionHypothesis (rowIndex + 1)
          (selectiveCompileExpr state (paddingRowExpr (n := n) row)).state
          ((selectiveCompileExpr state (paddingRowExpr (n := n) row)).output ::
            values) _ extraFuel finalOutput hrest
          (selectiveCompileExpr_ordered state _ hordered) hrecursiveBits rfl
          ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ hcontinueRest <;>
          simp [NPOracleState.write, NPOracleState.jump, hremainingTwo,
            hnextTwo, hselectedTwo, harityTwo, hrowWidthTwo, hfieldLimitTwo,
            hwidthTwo, hrowIndexRegTwo, hrowBaseTwo, hnodeCountTwo, hspineTwo,
            hbranchTwo]

/-- Interpreter fuel of the single output row, from the node loop's exit. -/
private def grammarOutputRowFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (extraFuel : ℕ) : ℕ :=
  3 +
    (10 +
      (selectiveGrammarCaseRunFuel state row 5 + (12 + (3 + extraFuel))))

/-- Register width of the single output row. -/
private def grammarOutputRowBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveGrammarCaseInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound)
        (boundedCircuitFieldLimit n bound) n row.val 5)) <|
    max (selectiveGrammarCaseRunBits state row 5) <|
      max
        (natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileExpr state (outputRowExpr (n := n) row))))) <|
        max
          (natBitLength
            (selectiveCountCasesSpineCode
              ((selectiveCompileExpr state
                (outputRowExpr (n := n) row)).output :: values))) <|
          max (natBitLength ((row.val + 1) * rowWidth n bound))
            (natBitLength (row.val + 1))

set_option maxHeartbeats 1600000 in
-- Three phase steps, the relocated grammar-case compiler at tag five, the
-- shared return block and the middle arm of the dispatch.
private theorem run_grammarOutputRow {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1))
    (branch rowIndex padRemaining maximumBits extraFuel finalOutput : ℕ)
    (values : List ℕ) (machine : NPOracleState)
    (hordered : selectiveStateOrdered state) (hrowIndex : row.val = rowIndex)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hbits : grammarOutputRowBits state row values ≤ maximumBits)
    (hpc : machine.pc = 34)
    (hframe :
      GrammarFrame state branch rowIndex 0 padRemaining
        (selectiveCountCasesSpineCode values) machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 37 →
      GrammarFrame (selectiveCompileExpr state (outputRowExpr (n := n) row)).state
        branch (rowIndex + 1) 0 padRemaining
        (selectiveCountCasesSpineCode
          ((selectiveCompileExpr state
            (outputRowExpr (n := n) row)).output :: values)) resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (grammarOutputRowFuel state row extraFuel) machine =
      some finalOutput := by
  simp only [grammarOutputRowBits] at hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hcalleeBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hwireBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hspineBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have hcursorBits := (Nat.le_max_left _ _).trans hbitsFour
  have hrowIndexBits := (Nat.le_max_right _ _).trans hbitsFour
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hcase : selectiveGrammarCaseExpr (n := n) row row.val 5 =
      outputRowExpr (n := n) row := selectiveGrammarCaseExpr_five row
  obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth,
    hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩ := hframe
  simp only [grammarOutputRowFuel]
  rw [show (3 : ℕ) +
      (10 +
        (selectiveGrammarCaseRunFuel state row 5 + (12 + (3 + extraFuel)))) =
    (10 + (selectiveGrammarCaseRunFuel state row 5 + (12 + (3 + extraFuel)))) +
      1 + 1 + 1 by omega]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 34) rfl) hpc
    (hsmall 5 (by omega))]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 35) rfl) rfl
    (hsmall 1 (by omega))]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 36) rfl) rfl]
  simp only [ite_self]
  refine run_grammarCaseCall state row branch rowIndex 0 padRemaining
    (selectiveCountCasesSpineCode values) 5 1 hordered hrowIndex maximumBits
    _ _ _ _ rfl hcalleeBits hrequestBits (by rw [hcase]; exact hwireBits)
    (hsmall 0 (by omega)) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ <;>
    try simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext,
      hselected, harity, hrowWidth, hfieldLimit, hwidth, hrowIndexReg, hrowBase,
      hnodeCount, hpadCount, hspine, hbranch]
  intro middle hmiddlePc hmiddleAccumulator hmiddlePhase hmiddleFrame
  rw [hcase] at hmiddleAccumulator
  refine run_grammarReturn state
    (selectiveCompileExpr state (outputRowExpr (n := n) row)) branch rowIndex 0
    padRemaining 1 values maximumBits _ _ middle hwireBits hspineBits
    (by rw [← hrowIndex]; exact hcursorBits)
    (by rw [← hrowIndex]; exact hrowIndexBits) (hsmall 1 (by omega)) hmiddlePc
    hmiddleAccumulator hmiddlePhase hmiddleFrame ?_
  intro resumed hresumedPc hresumedPhase hresumedFrame
  obtain ⟨hremainingTwo, hnextTwo, hselectedTwo, harityTwo, hrowWidthTwo,
    hfieldLimitTwo, hwidthTwo, hrowIndexRegTwo, hrowBaseTwo, hnodeCountTwo,
    hpadCountTwo, hspineTwo, hbranchTwo⟩ := hresumedFrame
  rw [show (3 : ℕ) + extraFuel = extraFuel + 1 + 1 + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 63) rfl) hresumedPc]
  rw [if_neg (by rw [hresumedPhase]; omega)]
  rw [run_decrement_instruction (value := 0)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 66) rfl) rfl
    (by simp [NPOracleState.jump, hresumedPhase])
    (hsmall 0 (by omega))]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 67) rfl) rfl]
  rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
  refine hcontinue _ rfl
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremainingTwo, hnextTwo,
      hselectedTwo, harityTwo, hrowWidthTwo, hfieldLimitTwo, hwidthTwo,
      hrowIndexRegTwo, hrowBaseTwo, hnodeCountTwo, hpadCountTwo, hspineTwo,
      hbranchTwo]

/-! ## 5. The reverse `and` fold

The exit path emits the canonical `true` base case and then one conjunction per
retained row, innermost first.  Interpreter resources are data dependent, so the
fold's clock and its register-width envelope follow the same recursion as its
output. -/

-- Four steps from the exhausted padding loop to the fold's constant base case.
private theorem run_grammarExit {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (branch rowIndex nodeRemaining spine : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 70)
    (hframe : GrammarFrame state branch rowIndex nodeRemaining 0 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 74 →
      resumed.registers 35 =
        rawCircuitNodeCode (n := descriptionWidth n bound) (.const true) →
      GrammarFrame state branch rowIndex nodeRemaining 0 spine resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (4 + extraFuel) machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth,
    hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩ := hframe
  have hnodeForm :
      rawCircuitNodeCode (n := descriptionWidth n bound) (.const true) =
        Nat.pair 0 1 := rfl
  rw [show 4 + extraFuel = extraFuel + 1 + 1 + 1 + 1 by omega]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 70) rfl) hpc
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 71) rfl) rfl
    (hsmall 1 (by omega))]
  rw [run_pair_instruction (value := Nat.pair 0 1)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 72) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hsmall (Nat.pair 0 1) (by decide))]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 73) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, hremaining, hnext,
      hselected, harity, hrowWidth, hfieldLimit, hwidth, hrowIndexReg, hrowBase,
      hnodeCount, hpadCount, hspine, hbranch]

set_option maxHeartbeats 1600000 in
-- Three request steps around the relocated append, then seven unpacking steps.
private theorem run_grammarEmitCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (node : BooleanNode (descriptionWidth n bound))
    (branch rowIndex nodeRemaining spine : ℕ)
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
    (hpc : machine.pc = 74)
    (hnode : machine.registers 35 = rawCircuitNodeCode node)
    (hframe : GrammarFrame state branch rowIndex nodeRemaining 0 spine machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 86 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 34 = (state.emit node).output →
      GrammarFrame (state.emit node).state branch rowIndex nodeRemaining 0
        spine resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit, hwidth,
    hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine, hbranch⟩ := hframe
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
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 74) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 75) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 76) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 77) rfl) rfl
    hzeroBits]
  rw [run_branchZero_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 78) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveFixedCountGrammarProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 79) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 80) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 81) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [run_unpairLeft_instruction
      (value := (state.emit node).state.target - (state.emit node).state.next)
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 82) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 83) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 84) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveFixedCountGrammarProgram_controllerAt (pc := 85) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowWidth, hfieldLimit, hwidth, hrowIndexReg, hrowBase, hnodeCount,
        hpadCount, hspine, hbranch]

/-- Interpreter fuel of the reverse fold from `86`. -/
private def grammarAndFoldFuel {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      10 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              grammarAndFoldFuel (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest)))

/-- Register width of the reverse fold from `86`. -/
private def grammarAndFoldBits {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
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
            grammarAndFoldBits (selectiveAnd state value accumulated).state
              (selectiveAnd state value accumulated).output rest

set_option maxHeartbeats 3200000 in
-- The fold is one induction on the retained spine.
private theorem run_grammarAndFoldLoop {n bound : ℕ}
    (branch rowIndex nodeRemaining maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (values : List ℕ)
      (state : SelectiveState (descriptionWidth n bound)) (accumulated : ℕ)
      (machine : NPOracleState),
      selectiveStateOrdered state →
      grammarAndFoldBits state accumulated values ≤ maximumBits →
      machine.pc = 86 →
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated →
      machine.registers 34 = accumulated →
      GrammarFrame state branch rowIndex nodeRemaining 0
        (selectiveCountCasesSpineCode values) machine →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          (grammarAndFoldFuel state accumulated values) machine =
        some
          (selectiveWireCode
            (selectiveUnaryFold state accumulated values)) := by
  intro values
  induction values with
  | nil =>
      intro state accumulated machine _ hbits hpc hwire _ hframe
      simp only [grammarAndFoldBits] at hbits
      simp only [grammarAndFoldFuel]
      rw [run_branchZero_instruction
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 86) rfl) hpc]
      rw [if_pos (by rw [hframe.2.2.2.2.2.2.2.2.2.2.2.1]; rfl)]
      exact run_halt_instruction (fuel := 0)
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 96) rfl) rfl
        (by rw [jump_registers_eq, hwire]; rfl) hbits
  | cons value rest inductionHypothesis =>
      intro state accumulated machine hordered hbits hpc hwire houtput hframe
      obtain ⟨hremaining, hnext, hselected, harity, hrowWidth, hfieldLimit,
        hwidth, hrowIndexReg, hrowBase, hnodeCount, hpadCount, hspine,
        hbranch⟩ := hframe
      simp only [grammarAndFoldBits] at hbits
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
          natBitLength (Nat.pair value (selectiveCountCasesSpineCode rest)) ≤
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
      have hspineNonzero : machine.registers 28 ≠ 0 := by
        rw [hspine, hspineForm]
        have hone :=
          Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
        omega
      simp only [grammarAndFoldFuel, selectiveUnaryFold]
      rw [show (10 : ℕ) +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                grammarAndFoldFuel (selectiveAnd state value accumulated).state
                  (selectiveAnd state value accumulated).output rest))) =
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              grammarAndFoldFuel (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest))) +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 86) rfl) hpc]
      rw [if_neg hspineNonzero]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (selectiveCountCasesSpineCode rest))
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 87) rfl) rfl
        (by rw [jump_registers_eq, hspine, hspineForm]; simp) hconsBits]
      rw [run_unpairLeft_instruction (value := value)
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 88) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      rw [run_unpairRight_instruction
        (value := selectiveCountCasesSpineCode rest)
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 89) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
      rw [run_add_instruction (value := descriptionWidth n bound + value)
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 90) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity])
        hleftChildBits]
      rw [run_add_instruction (value := descriptionWidth n bound + accumulated)
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 91) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity, houtput])
        hrightChildBits]
      rw [run_pair_instruction
        (value :=
          Nat.pair (descriptionWidth n bound + value)
            (descriptionWidth n bound + accumulated))
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 92) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
      rw [run_set_instruction
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 93) rfl) rfl
        (hsmall 3 (by omega))]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := descriptionWidth n bound)
            (.and value accumulated))
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 94) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
        hcodeBits]
      rw [run_branchZero_instruction
        (selectiveFixedCountGrammarProgram_controllerAt (pc := 95) rfl) rfl]
      simp only [ite_self]
      refine run_grammarEmitCall state (.and value accumulated) branch rowIndex
        nodeRemaining (selectiveCountCasesSpineCode rest) hordered maximumBits
        _ _ _ _ rfl hinputBits hwireBits (hsmall 0 (by omega)) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowWidth]
      · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
      · simp [NPOracleState.write, NPOracleState.jump, hwidth]
      · simp [NPOracleState.write, NPOracleState.jump, hrowIndexReg]
      · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
      · simp [NPOracleState.write, NPOracleState.jump, hnodeCount]
      · simp [NPOracleState.write, NPOracleState.jump, hpadCount]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, hbranch]
      · intro resumed hresumedPc hresumedWire hresumedOutput hresumedFrame
        exact inductionHypothesis (selectiveAnd state value accumulated).state
          (selectiveAnd state value accumulated).output resumed
          (selectiveState_emit_ordered state (.and value accumulated) hordered)
          hrecursiveBits hresumedPc hresumedWire hresumedOutput hresumedFrame

/-! ## 6. The request parser and the level runner -/

set_option maxHeartbeats 1600000 in
-- Twenty-two straight-line steps set up both loops' registers.
private theorem run_grammarPrologue {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (candidate : Fin bound)
    (branch maximumBits extraFuel finalOutput : ℕ) (entry : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveFixedCountGrammarInput (selectiveStateCode state)
            (descriptionWidth n bound) (rowWidth n bound)
            (boundedCircuitFieldLimit n bound) n bound candidate.val) ≤
        maximumBits)
    (hsuccBits : natBitLength (candidate.val + 1) ≤ maximumBits)
    (hpc : entry.pc = 0)
    (hbranch : entry.registers 29 = branch)
    (hinput :
      entry.registers 0 =
        selectiveFixedCountGrammarInput (selectiveStateCode state)
          (descriptionWidth n bound) (rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n bound candidate.val)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 22 →
      GrammarFrame state branch 0 (candidate.val + 1)
        (bound - (candidate.val + 1)) (selectiveCountCasesSpineCode [])
        resumed →
      runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
          extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveFixedCountGrammarProgram maximumBits
        (22 + extraFuel) entry =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveFixedCountGrammarInput] at hflat
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
  have hboundBits := natBitLength_pair_left hfive
  have hcandidateBits := natBitLength_pair_right hfive
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show (22 : ℕ) + extraFuel =
    extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 + 1 + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveFixedCountGrammarInput]) hstateBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (descriptionWidth n bound) <|
        Nat.pair (rowWidth n bound) <|
          Nat.pair (boundedCircuitFieldLimit n bound) <|
            Nat.pair n (Nat.pair bound candidate.val))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveFixedCountGrammarInput])
    hone]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairLeft_instruction (value := descriptionWidth n bound)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (rowWidth n bound) <|
        Nat.pair (boundedCircuitFieldLimit n bound) <|
          Nat.pair n (Nat.pair bound candidate.val))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [run_unpairLeft_instruction (value := rowWidth n bound)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit n bound) <|
        Nat.pair n (Nat.pair bound candidate.val))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [run_unpairLeft_instruction (value := boundedCircuitFieldLimit n bound)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair n (Nat.pair bound candidate.val))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [run_unpairLeft_instruction (value := n)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction (value := Nat.pair bound candidate.val)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [run_unpairLeft_instruction (value := bound)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hboundBits]
  rw [run_unpairRight_instruction (value := candidate.val)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcandidateBits]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 16) rfl) rfl
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 17) rfl) rfl
    (hsmall 0 (by omega))]
  rw [run_copy_instruction (value := candidate.val)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcandidateBits]
  rw [run_increment_instruction (value := candidate.val + 1)
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsuccBits]
  rw [run_subtract_instruction (value := bound - (candidate.val + 1))
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 20) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    ((natBitLength_mono (Nat.sub_le _ _)).trans hboundBits)]
  rw [run_set_instruction
    (selectiveFixedCountGrammarProgram_controllerAt (pc := 21) rfl) rfl
    (hsmall 0 (by omega))]
  refine hcontinue _ rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, selectiveCountCasesSpineCode,
      hbranch]

/-- The compiler state and retained spine after the node-row phase. -/
private def grammarAfterNodes {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) :
    SelectiveState (descriptionWidth n bound) × List ℕ :=
  grammarPass state (countNodeRows (n := n) candidate) []

/-- The compiler state and retained spine after the output row. -/
private def grammarAfterOutput {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) :
    SelectiveState (descriptionWidth n bound) × List ℕ :=
  grammarPass (grammarAfterNodes state candidate).1
    [outputRowExpr (n := n) (grammarOutputRow candidate)]
    (grammarAfterNodes state candidate).2

/-- The compiler state and retained spine after the padding phase. -/
private def grammarAfterPadding {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) :
    SelectiveState (descriptionWidth n bound) × List ℕ :=
  grammarPass (grammarAfterOutput state candidate).1
    (countPaddingRows (n := n) candidate)
    (grammarAfterOutput state candidate).2

private theorem grammarAfterNodes_eq {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) :
    grammarPass state
        ((fixedCountNodeRows candidate).map (nodeRowExpr (n := n))) [] =
      grammarAfterNodes state candidate := by
  rw [grammarAfterNodes, countNodeRows_eq_map]

private theorem grammarAfterPadding_eq {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) :
    grammarPass (grammarAfterOutput state candidate).1
        ((fixedCountPaddingRows candidate).map (paddingRowExpr (n := n)))
        (grammarAfterOutput state candidate).2 =
      grammarAfterPadding state candidate := by
  rw [grammarAfterPadding, countPaddingRows_eq_map]

/-- The fold's constant base case. -/
private def grammarBaseWire {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) : SelectiveWire (descriptionWidth n bound) :=
  selectiveConst (grammarAfterPadding state candidate).1 true

/-- Interpreter fuel of one whole fixed-count grammar compilation. -/
def selectiveFixedCountGrammarRunFuel {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) : ℕ :=
  22 +
    grammarNodeLoopFuel state (fixedCountNodeRows candidate)
      (grammarOutputRowFuel (grammarAfterNodes state candidate).1
        (grammarOutputRow candidate)
        (grammarPaddingLoopFuel (grammarAfterOutput state candidate).1
          (fixedCountPaddingRows candidate)
          (4 +
            (5 +
              (selectiveEmitFuel
                  ((grammarAfterPadding state candidate).1.target -
                    (grammarAfterPadding state candidate).1.next)
                  (selectiveSelectedCode
                    (grammarAfterPadding state candidate).1.selected) +
                (7 +
                  grammarAndFoldFuel (grammarBaseWire state candidate).state
                    (grammarBaseWire state candidate).output
                    (grammarAfterPadding state candidate).2))))))

/-- Register width of one whole fixed-count grammar compilation. -/
def selectiveFixedCountGrammarRunBits {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (candidate : Fin bound) : ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveFixedCountGrammarInput (selectiveStateCode state)
          (descriptionWidth n bound) (rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n bound candidate.val)) <|
      max (natBitLength (candidate.val + 1)) <|
        max (grammarNodeLoopBits state (fixedCountNodeRows candidate) []) <|
          max
            (grammarOutputRowBits (grammarAfterNodes state candidate).1
              (grammarOutputRow candidate)
              (grammarAfterNodes state candidate).2) <|
            max
              (grammarPaddingLoopBits (grammarAfterOutput state candidate).1
                (fixedCountPaddingRows candidate)
                (grammarAfterOutput state candidate).2) <|
              max
                (natBitLength
                  (selectiveEmitInput
                    ((grammarAfterPadding state candidate).1.target -
                      (grammarAfterPadding state candidate).1.next)
                    (grammarAfterPadding state candidate).1.next
                    (selectiveSelectedCode
                      (grammarAfterPadding state candidate).1.selected)
                    (rawCircuitNodeCode (n := descriptionWidth n bound)
                      (.const true)))) <|
                max
                  (natBitLength
                    (Nat.pair 0
                      (selectiveWireCode (grammarBaseWire state candidate)))) <|
                  grammarAndFoldBits (grammarBaseWire state candidate).state
                    (grammarBaseWire state candidate).output
                    (grammarAfterPadding state candidate).2

set_option maxHeartbeats 1600000 in
-- Twenty-two parser steps, the three phases and the reverse fold.
/-- **The fixed-count grammar compiler's run.**  The `1095`-instruction stream
started on its own ABI frame, at any entry registers, returns exactly the
compiler wire the source compiler produces for the candidate's exact grammar
predicate. -/
theorem run_selectiveFixedCountGrammarProgram {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound)) (candidate : Fin bound)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveFixedCountGrammarInput (selectiveStateCode state)
          (descriptionWidth n bound) (rowWidth n bound)
          (boundedCircuitFieldLimit n bound) n bound candidate.val) :
    runNPOracleProgram selectiveFixedCountGrammarProgram
        (selectiveFixedCountGrammarRunBits state candidate)
        (selectiveFixedCountGrammarRunFuel state candidate) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (fixedCountGrammarExpr (n := n) candidate))) := by
  have hbits :
      selectiveFixedCountGrammarRunBits state candidate ≤
        selectiveFixedCountGrammarRunBits state candidate := le_refl _
  unfold selectiveFixedCountGrammarRunBits at hbits
  have hsevenBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hsuccBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hnodeLoopBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have houtputRowBits := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hpaddingLoopBits := (Nat.le_max_left _ _).trans hbitsFive
  have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
  have hemitInputBits := (Nat.le_max_left _ _).trans hbitsSix
  have hbitsSeven := (Nat.le_max_right _ _).trans hbitsSix
  have hemitWireBits := (Nat.le_max_left _ _).trans hbitsSeven
  have hfoldBits := (Nat.le_max_right _ _).trans hbitsSeven
  have hsmall : ∀ value : ℕ, value ≤ 7 →
      natBitLength value ≤ selectiveFixedCountGrammarRunBits state candidate :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have horderedNodes :
      selectiveStateOrdered (grammarAfterNodes state candidate).1 :=
    grammarPass_ordered _ _ _ hordered
  have horderedOutput :
      selectiveStateOrdered (grammarAfterOutput state candidate).1 :=
    grammarPass_ordered _ _ _ horderedNodes
  have horderedPadding :
      selectiveStateOrdered (grammarAfterPadding state candidate).1 :=
    grammarPass_ordered _ _ _ horderedOutput
  have hpass :
      grammarPass state (fixedCountGrammarExprs (n := n) candidate) [] =
        grammarAfterPadding state candidate := by
    unfold fixedCountGrammarExprs
    rw [grammarPass_append]
    rfl
  have hfold :
      selectiveCompileExpr state (fixedCountGrammarExpr (n := n) candidate) =
        selectiveUnaryFold (grammarBaseWire state candidate).state
          (grammarBaseWire state candidate).output
          (grammarAfterPadding state candidate).2 := by
    rw [← boolExpr_all_fixedCountGrammarExprs candidate,
      selectiveCompileExpr_all_eq_fold]
    have hpair := hpass
    rw [grammarPass_eq] at hpair
    have hstate :
        (selectiveUnaryHeads state
          (fixedCountGrammarExprs (n := n) candidate)).state =
          (grammarAfterPadding state candidate).1 := congrArg Prod.fst hpair
    have hvalues :
        (selectiveUnaryHeads state
            (fixedCountGrammarExprs (n := n) candidate)).values.reverse =
          (grammarAfterPadding state candidate).2 := by
      have := congrArg Prod.snd hpair
      simpa using this
    rw [hstate, hvalues]
    rfl
  rw [hfold]
  unfold selectiveFixedCountGrammarRunFuel
  refine run_grammarPrologue state candidate (entry.registers 29) _ _ _ entry
    hsevenBits hrequestBits hsuccBits hentryPc rfl hentryInput ?_
  intro afterPrologue hprologuePc hprologueFrame
  refine run_grammarNodeLoop (entry.registers 29) (bound - (candidate.val + 1))
    _ hsevenBits (fixedCountNodeRows candidate) 0 state [] afterPrologue _ _
    (grammarRowsFrom_nodeRows candidate) hordered hnodeLoopBits hprologuePc
    ?_ ?_
  · rw [fixedCountNodeRows_length]
    exact hprologueFrame
  intro afterNodes hnodesPc hnodesFrame
  rw [grammarAfterNodes_eq] at hnodesFrame
  rw [fixedCountNodeRows_length, Nat.zero_add] at hnodesFrame
  refine run_grammarOutputRow (grammarAfterNodes state candidate).1
    (grammarOutputRow candidate) (entry.registers 29) (candidate.val + 1)
    (bound - (candidate.val + 1)) _ _ _
    (grammarAfterNodes state candidate).2 afterNodes horderedNodes rfl
    hsevenBits houtputRowBits hnodesPc hnodesFrame ?_
  intro afterOutput houtputPc houtputFrame
  rw [← fixedCountPaddingRows_length candidate] at houtputFrame
  refine run_grammarPaddingLoop (entry.registers 29) 0 _ hsevenBits
    (fixedCountPaddingRows candidate) (candidate.val + 2)
    (grammarAfterOutput state candidate).1
    (grammarAfterOutput state candidate).2 afterOutput _ _
    (grammarRowsFrom_paddingRows candidate) horderedOutput hpaddingLoopBits
    houtputPc houtputFrame ?_
  intro afterPadding hpaddingPc hpaddingFrame
  rw [grammarAfterPadding_eq] at hpaddingFrame
  refine run_grammarExit (grammarAfterPadding state candidate).1
    (entry.registers 29) _ 0 _ _ _ _ afterPadding hsevenBits hpaddingPc
    hpaddingFrame ?_
  intro afterBase hbasePc hbaseNode hbaseFrame
  refine run_grammarEmitCall (grammarAfterPadding state candidate).1
    (.const true) (entry.registers 29) _ 0 _ horderedPadding _ _ _ _ afterBase
    rfl hemitInputBits hemitWireBits (hsmall 0 (by omega)) hbasePc hbaseNode
    hbaseFrame ?_
  intro afterEmit hemitPc hemitWire hemitOutput hemitFrame
  exact run_grammarAndFoldLoop (entry.registers 29) _ 0 _ hsevenBits
    (grammarAfterPadding state candidate).2
    (grammarBaseWire state candidate).state
    (grammarBaseWire state candidate).output afterEmit
    (selectiveState_emit_ordered _ _ horderedPadding) hfoldBits hemitPc
    hemitWire hemitOutput hemitFrame

/-- **Level premise, discharged.**  The fixed-count grammar compiler's run at
its own ABI frame, packaged in the runner shape the fixed-count controller one
level up consumes.  Nothing on this level is left as a premise. -/
def selectiveFixedCountGrammarRunner (width bound : ℕ) :
    SelectiveFixedCountGrammarRunner width bound where
  bits state candidate := selectiveFixedCountGrammarRunBits state candidate
  fuel state candidate := selectiveFixedCountGrammarRunFuel state candidate
  executes := by
    intro state candidate hordered entry hentryPc hentryInput
    exact run_selectiveFixedCountGrammarProgram state candidate hordered entry
      hentryPc hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
