import Proof.Supplier.SelectiveFieldSelectRun

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

open private selectiveAddressSelectInput
  selectiveAddressSelectControllerProgram
  selectiveAddressSelectControllerProgram_length selectiveAddressSelectProgram
  selectiveAddressSelectProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The controller's two passes, at the typed level -/

/-- **The controller's scheduling identity for disjunctions.**  The source
compiler's right-associated `any` is exactly the forward pass over its
disjuncts followed by the reverse fold over the retained spine. -/
theorem selectiveCompileExpr_any_eq_fold {n : ℕ}
    (expressions : List (BoolExpr n)) (state : SelectiveState n) :
    selectiveCompileExpr state (BoolExpr.any expressions) =
      selectiveCountCasesFold
        (selectiveConst (selectiveUnaryHeads state expressions).state
          false).state
        (selectiveConst (selectiveUnaryHeads state expressions).state
          false).output
        (selectiveUnaryHeads state expressions).values.reverse := by
  induction expressions generalizing state with
  | nil => rfl
  | cons expression rest ih =>
      simp only [BoolExpr.any, selectiveCompileExpr, selectiveUnaryHeads,
        List.reverse_cons]
      rw [selectiveCountCasesFold_concat]
      rw [ih]

def selectiveAddressSelectExpr {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode index : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    BoolExpr (descriptionWidth n bound) :=
  if addressCode.testBit index then
    unaryEqualsExpr row start limit index hblock
  else
    BoolExpr.const false

/-- The compiled wire of one disjunct. -/
def selectiveAddressSelectWire {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCompileExpr state
    (selectiveAddressSelectExpr row start limit addressCode index hblock)

theorem selectiveAddressSelectWire_ordered {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveAddressSelectWire row start limit addressCode hblock state
        index).state :=
  selectiveCompileExpr_ordered state _ hordered

/-- The disjunct list the controller walks from one starting bit index and one
countdown. -/
def selectiveAddressSelectExprs {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    ℕ → ℕ → List (BoolExpr (descriptionWidth n bound))
  | _, 0 => []
  | index, remaining + 1 =>
      selectiveAddressSelectExpr row start limit addressCode index hblock ::
        selectiveAddressSelectExprs row start limit addressCode hblock
          (index + 1) remaining

/-! ## 2. Decoding the fixed 195-instruction stream -/

private theorem selectiveAddressSelectProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveAddressSelectControllerProgram 80 177)[pc]? =
        some instruction) :
    selectiveAddressSelectProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveAddressSelectControllerProgram 80 177).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveAddressSelectControllerProgram_length] at hpc
  simp only [selectiveAddressSelectProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveAddressSelectControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveAddressSelectControllerProgram_length]
    omega)]
  exact hlookup

theorem selectiveAddressSelectProgram_unaryCallable :
    ProgramCallableAt selectiveAddressSelectProgram selectiveUnaryProgram
      80 1000 50 69 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveUnaryProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUnaryProgram_length] at hpc
  simp only [selectiveAddressSelectProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveAddressSelectControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveAddressSelectControllerProgram_length]
    omega)]
  simp only [selectiveAddressSelectControllerProgram_length]
  rw [show 80 + pc - 80 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem selectiveAddressSelectProgram_emitCallable :
    ProgramCallableAt selectiveAddressSelectProgram selectiveEmitProgram
      177 2000 50 69 := by
  intro pc instruction hlookup
  simp only [selectiveAddressSelectProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveAddressSelectControllerProgram_length,
      selectiveUnaryProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveAddressSelectControllerProgram_length,
    selectiveUnaryProgram_length]
  rw [show 177 + pc - (80 + 97) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The two shared call frames

Both append sites reach the relocated append through the physical block at
`64`; both unary sites reach the relocated unary compiler through the block at
`55`.  Each block builds the callee's request from the live state registers,
runs the callee, and unpacks the returned wire back into those registers;
both then fall through to the shared phase dispatcher at `76`. -/

private theorem run_selectiveAddressSelectEmitCall {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity rowBase start limit width addressCode bitIndex spine countdown
      accumulated phase : ℕ)
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
    (hpc : machine.pc = 64)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 21 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hrowBase : machine.registers 10 = rowBase)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hwidth : machine.registers 15 = width)
    (haddress : machine.registers 16 = addressCode)
    (hbitIndex : machine.registers 17 = bitIndex)
    (hspine : machine.registers 18 = spine)
    (hcountdown : machine.registers 19 = countdown)
    (haccumulated : machine.registers 28 = accumulated)
    (hphase : machine.registers 30 = phase)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 76 →
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
      resumed.registers 15 = width →
      resumed.registers 16 = addressCode →
      resumed.registers 17 = bitIndex →
      resumed.registers 18 = spine →
      resumed.registers 19 = countdown →
      resumed.registers 28 = accumulated →
      resumed.registers 30 = phase →
      runNPOracleProgram selectiveAddressSelectProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveAddressSelectProgram maximumBits
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
    (selectiveAddressSelectProgram_controllerAt (pc := 64) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveAddressSelectProgram_controllerAt (pc := 65) rfl) rfl
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
    (selectiveAddressSelectProgram_controllerAt (pc := 66) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 67) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 68) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveAddressSelectProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (state.emit node))
      (selectiveAddressSelectProgram_controllerAt (pc := 69) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveAddressSelectProgram_controllerAt (pc := 70) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveAddressSelectProgram_controllerAt (pc := 71) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (state.emit node).state.target - (state.emit node).state.next)
      (selectiveAddressSelectProgram_controllerAt (pc := 72) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveAddressSelectProgram_controllerAt (pc := 73) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveAddressSelectProgram_controllerAt (pc := 74) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveAddressSelectProgram_controllerAt (pc := 75) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hstart, hlimit, hwidth, haddress, hbitIndex, hspine,
        hcountdown, haccumulated, hphase]

private theorem run_selectiveAddressSelectUnaryCall {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit index : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (maximumBits unaryFuel extraFuel finalOutput : ℕ)
    (width addressCode spine countdown accumulated phase : ℕ)
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
              (selectiveCompileExpr state
                (unaryEqualsExpr (n := n) row start limit index hblock)))) ≤
        maximumBits)
    (hpc : machine.pc = 55)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth n bound)
    (hrowBase : machine.registers 10 = row.val * rowWidth n bound)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (hwidth : machine.registers 15 = width)
    (haddress : machine.registers 16 = addressCode)
    (hbitIndex : machine.registers 17 = index)
    (hspine : machine.registers 18 = spine)
    (hcountdown : machine.registers 19 = countdown)
    (haccumulated : machine.registers 28 = accumulated)
    (hphase : machine.registers 30 = phase)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 76 →
      resumed.registers 4 =
        (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index
              hblock)).state.target -
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index
              hblock)).state.next →
      resumed.registers 6 =
        (selectiveCompileExpr state
          (unaryEqualsExpr (n := n) row start limit index hblock)).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index
              hblock)).state.selected →
      resumed.registers 25 =
        (selectiveCompileExpr state
          (unaryEqualsExpr (n := n) row start limit index hblock)).output →
      resumed.registers 8 = descriptionWidth n bound →
      resumed.registers 10 = row.val * rowWidth n bound →
      resumed.registers 12 = start →
      resumed.registers 14 = limit →
      resumed.registers 15 = width →
      resumed.registers 16 = addressCode →
      resumed.registers 17 = index →
      resumed.registers 18 = spine →
      resumed.registers 19 = countdown →
      resumed.registers 28 = accumulated →
      resumed.registers 30 = phase →
      runNPOracleProgram selectiveAddressSelectProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveAddressSelectProgram maximumBits
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
    (selectiveAddressSelectProgram_controllerAt (pc := 55) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 8 + (unaryFuel + (7 + extraFuel)) =
    (7 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveAddressSelectProgram_controllerAt (pc := 56) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hremaining,
        hstateForm state])
    hstateBits]
  rw [show 7 + (unaryFuel + (7 + extraFuel)) =
    (6 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair limit index)
    (selectiveAddressSelectProgram_controllerAt (pc := 57) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hlimit, hbitIndex])
    htailFour]
  rw [show 6 + (unaryFuel + (7 + extraFuel)) =
    (5 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair start (Nat.pair limit index))
    (selectiveAddressSelectProgram_controllerAt (pc := 58) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstart]) htailThree]
  rw [show 5 + (unaryFuel + (7 + extraFuel)) =
    (4 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (row.val * rowWidth n bound)
        (Nat.pair start (Nat.pair limit index)))
    (selectiveAddressSelectProgram_controllerAt (pc := 59) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowBase]) htailTwo]
  rw [show 4 + (unaryFuel + (7 + extraFuel)) =
    (3 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth n bound)
        (Nat.pair (row.val * rowWidth n bound)
          (Nat.pair start (Nat.pair limit index))))
    (selectiveAddressSelectProgram_controllerAt (pc := 60) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) htailOne]
  rw [show 3 + (unaryFuel + (7 + extraFuel)) =
    (2 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
        (row.val * rowWidth n bound) start limit index)
    (selectiveAddressSelectProgram_controllerAt (pc := 61) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [show 2 + (unaryFuel + (7 + extraFuel)) =
    (1 + (unaryFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 62) rfl) rfl hzeroBits]
  rw [show 1 + (unaryFuel + (7 + extraFuel)) =
    (unaryFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 63) rfl) rfl]
  simp only [ite_self]
  rw [hunaryFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveUnaryProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileExpr state
          (unaryEqualsExpr (n := n) row start limit index hblock)))
    selectiveAddressSelectProgram_unaryCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
  · intro _unaryHalt
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index hblock)))
      (selectiveAddressSelectProgram_controllerAt (pc := 69) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index hblock)).state)
      (selectiveAddressSelectProgram_controllerAt (pc := 70) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveCompileExpr state
          (unaryEqualsExpr (n := n) row start limit index hblock)).output)
      (selectiveAddressSelectProgram_controllerAt (pc := 71) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index
              hblock)).state.target -
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index
              hblock)).state.next)
      (selectiveAddressSelectProgram_controllerAt (pc := 72) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index hblock)).state.next
          (selectiveSelectedCode
            (selectiveCompileExpr state
              (unaryEqualsExpr (n := n) row start limit index
                hblock)).state.selected))
      (selectiveAddressSelectProgram_controllerAt (pc := 73) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileExpr state
          (unaryEqualsExpr (n := n) row start limit index hblock)).state.next)
      (selectiveAddressSelectProgram_controllerAt (pc := 74) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit index
              hblock)).state.selected)
      (selectiveAddressSelectProgram_controllerAt (pc := 75) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hrowBase, hstart, hlimit, hwidth, haddress, hbitIndex, hspine,
        hcountdown, haccumulated, hphase]

/-! ## 4. The reverse disjunction fold -/

/-- Interpreter fuel of the reverse fold: eleven controller steps, one
relocated append, and a six-step phase dispatch per retained disjunct. -/
def selectiveAddressSelectFoldFuel {n : ℕ} :
    SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      11 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              (6 +
                selectiveAddressSelectFoldFuel
                  (selectiveOr state value accumulated).state
                  (selectiveOr state value accumulated).output rest))))

private theorem run_selectiveAddressSelectFoldStep {n : ℕ}
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
    (hpc : machine.pc = 41)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hspine :
      machine.registers 18 = selectiveCountCasesSpineCode (value :: rest))
    (haccumulated : machine.registers 28 = accumulated)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 41 →
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
      resumed.registers 18 = selectiveCountCasesSpineCode rest →
      resumed.registers 28 = (selectiveOr state value accumulated).output →
      runNPOracleProgram selectiveAddressSelectProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveAddressSelectProgram maximumBits
        (11 + (5 + (emitFuel + (7 + (6 + extraFuel))))) machine =
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
  have hspineNonzero : machine.registers 18 ≠ 0 := by
    rw [hspine, hspineForm]
    have hone :=
      Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
    omega
  rw [show 11 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (10 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 41) rfl) hpc]
  rw [if_neg hspineNonzero]
  rw [show 10 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (9 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair value (selectiveCountCasesSpineCode rest))
    (selectiveAddressSelectProgram_controllerAt (pc := 42) rfl) rfl
    (by simp [NPOracleState.jump, hspine, hspineForm]) hconsBits]
  rw [show 9 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (8 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_unpairLeft_instruction (value := value)
    (selectiveAddressSelectProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 8 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (7 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveCountCasesSpineCode rest)
    (selectiveAddressSelectProgram_controllerAt (pc := 44) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
  rw [show 7 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (6 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_add_instruction (value := n + value)
    (selectiveAddressSelectProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hleftChildBits]
  rw [show 6 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (5 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_add_instruction (value := n + accumulated)
    (selectiveAddressSelectProgram_controllerAt (pc := 46) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, haccumulated])
    hrightChildBits]
  rw [show 5 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (4 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + value) (n + accumulated))
    (selectiveAddressSelectProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 4 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (3 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 48) rfl) rfl hfourBits]
  rw [show 3 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (2 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.or value accumulated))
    (selectiveAddressSelectProgram_controllerAt (pc := 49) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 2 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (1 + (5 + (emitFuel + (7 + (6 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 50) rfl) rfl htwoBits]
  rw [show 1 + (5 + (emitFuel + (7 + (6 + extraFuel)))) =
    (5 + (emitFuel + (7 + (6 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 51) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveAddressSelectEmitCall state (.or value accumulated)
    hordered maximumBits emitFuel (6 + extraFuel) finalOutput n
    (machine.registers 10) (machine.registers 12) (machine.registers 14)
    (machine.registers 15) (machine.registers 16) (machine.registers 17)
    (selectiveCountCasesSpineCode rest) (machine.registers 19)
    (n + accumulated) 2 _ hemitFuel hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
      hresumedSelected hresumedOutput hresumedArity _ _ _ _ _ _ hresumedSpine
      _ _ hresumedPhase
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveAddressSelectProgram_controllerAt (pc := 76) rfl) hresumedPc]
    rw [if_neg (by simp [hresumedPhase])]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := 1)
      (selectiveAddressSelectProgram_controllerAt (pc := 77) rfl) rfl
      (by simp [NPOracleState.jump, hresumedPhase]) honeBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveAddressSelectProgram_controllerAt (pc := 78) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveAddressSelectProgram_controllerAt (pc := 79) rfl) rfl]
    simp only [ite_self]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_copy_instruction
      (value := (selectiveOr state value accumulated).output)
      (selectiveAddressSelectProgram_controllerAt (pc := 52) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, selectiveOr,
          hresumedOutput])
      hnextOutputBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveAddressSelectProgram_controllerAt (pc := 53) rfl) rfl]
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

private theorem run_selectiveAddressSelectFoldLoop {n : ℕ}
    (values : List ℕ) (state : SelectiveState n) (accumulated : ℕ)
    (hordered : selectiveStateOrdered state) (maximumBits : ℕ)
    (hbits :
      natBitLength
          (selectiveCountCasesFoldWorkBound state accumulated values) ≤
        maximumBits)
    (machine : NPOracleState) (hpc : machine.pc = 41)
    (hwire :
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode values)
    (haccumulated : machine.registers 28 = accumulated) :
    runNPOracleProgram selectiveAddressSelectProgram maximumBits
        (selectiveAddressSelectFoldFuel state accumulated values) machine =
      some
        (selectiveWireCode
          (selectiveCountCasesFold state accumulated values)) := by
  induction values generalizing state accumulated machine with
  | nil =>
      have hfuel :
          selectiveAddressSelectFoldFuel state accumulated ([] : List ℕ) =
            (0 + 1) + 1 := rfl
      have hfoldNil :
          selectiveWireCode
              (selectiveCountCasesFold state accumulated ([] : List ℕ)) =
            Nat.pair (selectiveStateCode state) accumulated := rfl
      rw [hfuel]
      rw [run_branchZero_instruction
        (selectiveAddressSelectProgram_controllerAt (pc := 41) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      refine run_halt_instruction (fuel := 0)
        (selectiveAddressSelectProgram_controllerAt (pc := 54) rfl) rfl ?_ ?_
      · rw [hfoldNil]
        exact hwire
      · rw [hfoldNil]
        exact hbits
  | cons value rest ih =>
      have hfuel :
          selectiveAddressSelectFoldFuel state accumulated (value :: rest) =
            11 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    (6 +
                      selectiveAddressSelectFoldFuel
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
      refine run_selectiveAddressSelectFoldStep state accumulated value rest
        hordered maximumBits _ _ _ machine rfl hspineBits hinputBits hwireBits
        hpc hremaining hnext hselected harity hspine haccumulated ?_
      intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedSpine hresumedAccumulated
      exact ih _ _
        (selectiveState_emit_ordered state (.or value accumulated) hordered)
        hrecBits _ hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedSpine hresumedAccumulated

/-! ## 5. The forward address-bit pass -/

/-- The wire the controller is committed to once it reaches the bit loop head
with the given retained spine. -/
def selectiveAddressSelectForwardOutput {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound))
    (index remaining : ℕ) (spine : List ℕ) :
    SelectiveWire (descriptionWidth n bound) :=
  selectiveCountCasesFold
    (selectiveConst
      (selectiveUnaryHeads state
        (selectiveAddressSelectExprs row start limit addressCode hblock index
          remaining)).state false).state
    (selectiveConst
      (selectiveUnaryHeads state
        (selectiveAddressSelectExprs row start limit addressCode hblock index
          remaining)).state false).output
    ((selectiveUnaryHeads state
      (selectiveAddressSelectExprs row start limit addressCode hblock index
        remaining)).values.reverse ++ spine)

private theorem selectiveAddressSelectForwardOutput_nil {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (spine : List ℕ) :
    selectiveAddressSelectForwardOutput row start limit addressCode hblock
        state index 0 spine =
      selectiveCountCasesFold (selectiveConst state false).state
        (selectiveConst state false).output spine := rfl

private theorem selectiveAddressSelectForwardOutput_succ {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound))
    (index remaining : ℕ) (spine : List ℕ) :
    selectiveAddressSelectForwardOutput row start limit addressCode hblock
        state index (remaining + 1) spine =
      selectiveAddressSelectForwardOutput row start limit addressCode hblock
        (selectiveAddressSelectWire row start limit addressCode hblock state index).state (index +
          1) remaining
        ((selectiveAddressSelectWire row start limit addressCode hblock state index).output ::
          spine) := by
  simp only [selectiveAddressSelectForwardOutput, selectiveAddressSelectExprs,
    selectiveUnaryHeads, selectiveAddressSelectWire, List.reverse_cons,
    List.append_assoc, List.singleton_append]

/-- Interpreter fuel of the whole controller from the bit loop head. -/
def selectiveAddressSelectForwardFuel {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    SelectiveState (descriptionWidth n bound) → ℕ → ℕ → List ℕ → ℕ
  | state, _, 0, spine =>
      1 +
        (5 +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                (4 +
                  selectiveAddressSelectFoldFuel
                    (selectiveConst state false).state
                    (selectiveConst state false).output spine)))))
  | state, index, remaining + 1, spine =>
      if addressCode.testBit index then
        5 +
          (9 +
            (selectiveUnaryRunFuel state (selectiveUnaryEqualsLiterals (n := n) row start limit
              index hblock) +
              (7 + (1 + (6 + selectiveAddressSelectForwardFuel row start limit addressCode hblock
                (selectiveAddressSelectWire row start limit addressCode hblock state index).state
                  (index + 1) remaining
                ((selectiveAddressSelectWire row start limit addressCode hblock state index).output
                  :: spine))))))
      else
        8 +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 + (1 + (6 + selectiveAddressSelectForwardFuel row start limit addressCode hblock
                (selectiveAddressSelectWire row start limit addressCode hblock state index).state
                  (index + 1) remaining
                ((selectiveAddressSelectWire row start limit addressCode hblock state index).output
                  :: spine))))))

/-- Register-width envelope of the whole controller from the bit loop head. -/
def selectiveAddressSelectForwardBits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    SelectiveState (descriptionWidth n bound) → ℕ → ℕ → List ℕ → ℕ
  | state, _, 0, spine =>
      max (natBitLength 1) <|
        max
          (natBitLength
            (selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)))) <|
          max
            (natBitLength
              (Nat.pair 0 (selectiveWireCode (selectiveConst state false)))) <|
            natBitLength
              (selectiveCountCasesFoldWorkBound
                (selectiveConst state false).state
                (selectiveConst state false).output spine)
  | state, index, remaining + 1, spine =>
      if addressCode.testBit index then
        max
          (selectiveUnaryRunBits state (selectiveUnaryEqualsLiterals (n := n) row start limit index
            hblock)
            (row.val * rowWidth n bound) start index) <|
          max
            (natBitLength
              (selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
                (row.val * rowWidth n bound) start limit index)) <|
            max
              (natBitLength
                (Nat.pair 0 (selectiveWireCode (selectiveAddressSelectWire row start limit
                  addressCode hblock state index)))) <|
              max (natBitLength (index + 1)) <|
                max (natBitLength remaining) <|
                  max
                    (natBitLength
                      (selectiveCountCasesSpineCode
                        ((selectiveAddressSelectWire row start limit addressCode hblock state
                          index).output :: spine))) <|
                    selectiveAddressSelectForwardBits row start limit addressCode hblock
                (selectiveAddressSelectWire row start limit addressCode hblock state index).state
                  (index + 1) remaining
                ((selectiveAddressSelectWire row start limit addressCode hblock state index).output
                  :: spine)
      else
        max
          (natBitLength
            (selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)))) <|
          max
            (natBitLength
              (Nat.pair 0 (selectiveWireCode (selectiveAddressSelectWire row start limit
                addressCode hblock state index)))) <|
            max (natBitLength (index + 1)) <|
              max (natBitLength remaining) <|
                max
                  (natBitLength
                    (selectiveCountCasesSpineCode
                      ((selectiveAddressSelectWire row start limit addressCode hblock state
                        index).output :: spine))) <|
                  selectiveAddressSelectForwardBits row start limit addressCode hblock
                (selectiveAddressSelectWire row start limit addressCode hblock state index).state
                  (index + 1) remaining
                ((selectiveAddressSelectWire row start limit addressCode hblock state index).output
                  :: spine)

private theorem run_selectiveAddressSelectForwardLoop {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) (remaining : ℕ)
    (state : SelectiveState (descriptionWidth n bound)) (index : ℕ)
    (spine : List ℕ) (maximumBits : ℕ)
    (hordered : selectiveStateOrdered state)
    (hbits :
      selectiveAddressSelectForwardBits row start limit addressCode hblock
        state index remaining spine ≤ maximumBits)
    (machine : NPOracleState) (hpc : machine.pc = 19)
    (hremainingReg : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = descriptionWidth n bound)
    (hrowBase : machine.registers 10 = row.val * rowWidth n bound)
    (hstart : machine.registers 12 = start)
    (hlimit : machine.registers 14 = limit)
    (haddress : machine.registers 16 = addressCode)
    (hbitIndex : machine.registers 17 = index)
    (hspine : machine.registers 18 = selectiveCountCasesSpineCode spine)
    (hcountdown : machine.registers 19 = remaining) :
    runNPOracleProgram selectiveAddressSelectProgram maximumBits
        (selectiveAddressSelectForwardFuel row start limit addressCode hblock
          state index remaining spine) machine =
      some
        (selectiveWireCode
          (selectiveAddressSelectForwardOutput row start limit addressCode
            hblock state index remaining spine)) := by
  induction remaining generalizing state index spine machine with
  | zero =>
      obtain ⟨emitFuel, hemitFuelEq⟩ :
          ∃ fuel,
            selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) = fuel := ⟨_, rfl⟩
      obtain ⟨foldFuel, hfoldFuelEq⟩ :
          ∃ fuel,
            selectiveAddressSelectFoldFuel (selectiveConst state false).state
                (selectiveConst state false).output spine = fuel := ⟨_, rfl⟩
      have hfuel :
          selectiveAddressSelectForwardFuel row start limit addressCode hblock
              state index 0 spine =
            1 + (5 + (5 + (emitFuel + (7 + (4 + foldFuel))))) := by
        rw [← hemitFuelEq, ← hfoldFuelEq]
        rfl
      have hbitsNil :
          selectiveAddressSelectForwardBits row start limit addressCode hblock
              state index 0 spine =
            max (natBitLength 1)
              (max
                (natBitLength
                  (selectiveEmitInput (state.target - state.next) state.next
                    (selectiveSelectedCode state.selected)
                    (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false))))
                (max
                  (natBitLength
                    (Nat.pair 0
                      (selectiveWireCode (selectiveConst state false))))
                  (natBitLength
                    (selectiveCountCasesFoldWorkBound
                      (selectiveConst state false).state
                      (selectiveConst state false).output spine)))) := rfl
      rw [hbitsNil] at hbits
      have honeBits := (Nat.le_max_left _ _).trans hbits
      have hbitsTail := (Nat.le_max_right _ _).trans hbits
      have hinputBits := (Nat.le_max_left _ _).trans hbitsTail
      have hbitsTailTwo := (Nat.le_max_right _ _).trans hbitsTail
      have hwireBits := (Nat.le_max_left _ _).trans hbitsTailTwo
      have hfoldBits := (Nat.le_max_right _ _).trans hbitsTailTwo
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        (natBitLength_mono (Nat.zero_le _)).trans honeBits
      have hnodeCode :
          rawCircuitNodeCode (n := descriptionWidth n bound) (.const false) = Nat.pair 0 0 := rfl
      have hemitInput :
          selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)) =
            Nat.pair (selectiveStateCode state)
              (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)) := rfl
      have hcodeBits :
          natBitLength (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hinputBits
        rw [hemitInput]
        exact Nat.right_le_pair _ _
      have hconstOutputBits :
          natBitLength (selectiveConst state false).output ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans
          ((natBitLength_mono (Nat.right_le_pair 0 _)).trans hwireBits)
        exact Nat.right_le_pair _ _
      rw [hfuel, selectiveAddressSelectForwardOutput_nil]
      rw [show 1 + (5 + (5 + (emitFuel + (7 + (4 + foldFuel))))) = (5 + (5 + (emitFuel + (7 + (4 +
        foldFuel))))) + 1 by
        omega]
      rw [run_branchZero_instruction
        (selectiveAddressSelectProgram_controllerAt (pc := 19) rfl) hpc]
      rw [if_pos (by rw [hcountdown])]
      rw [show 5 + (5 + (emitFuel + (7 + (4 + foldFuel)))) =
        (4 + (5 + (emitFuel + (7 + (4 + foldFuel))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveAddressSelectProgram_controllerAt (pc := 35) rfl) rfl
        hzeroBits]
      rw [show 4 + (5 + (emitFuel + (7 + (4 + foldFuel)))) =
        (3 + (5 + (emitFuel + (7 + (4 + foldFuel))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveAddressSelectProgram_controllerAt (pc := 36) rfl) rfl
        hzeroBits]
      rw [show 3 + (5 + (emitFuel + (7 + (4 + foldFuel)))) =
        (2 + (5 + (emitFuel + (7 + (4 + foldFuel))))) + 1 by omega]
      rw [run_pair_instruction
        (value := rawCircuitNodeCode (n := descriptionWidth n bound) (.const false))
        (selectiveAddressSelectProgram_controllerAt (pc := 37) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode])
        hcodeBits]
      rw [show 2 + (5 + (emitFuel + (7 + (4 + foldFuel)))) =
        (1 + (5 + (emitFuel + (7 + (4 + foldFuel))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveAddressSelectProgram_controllerAt (pc := 38) rfl) rfl
        honeBits]
      rw [show 1 + (5 + (emitFuel + (7 + (4 + foldFuel)))) =
        (5 + (emitFuel + (7 + (4 + foldFuel)))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveAddressSelectProgram_controllerAt (pc := 39) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveAddressSelectEmitCall state (.const false) hordered
        maximumBits emitFuel (4 + foldFuel) _ (descriptionWidth n bound)
        (row.val * rowWidth n bound) start limit (machine.registers 15)
        addressCode index (selectiveCountCasesSpineCode spine) 0
        (machine.registers 28) 1 _ hemitFuelEq.symm hinputBits hwireBits ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rfl
      · simp [NPOracleState.write, NPOracleState.jump, hremainingReg]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
      · simp [NPOracleState.write, NPOracleState.jump, hstart]
      · simp [NPOracleState.write, NPOracleState.jump, hlimit]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, haddress]
      · simp [NPOracleState.write, NPOracleState.jump, hbitIndex]
      · simp [NPOracleState.write, NPOracleState.jump, hspine]
      · simp [NPOracleState.write, NPOracleState.jump, hcountdown]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
          hresumedSelected hresumedOutput hresumedArity _ _ _ _ _ _
          hresumedSpine _ _ hresumedPhase
        rw [show 4 + foldFuel = (3 + foldFuel) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveAddressSelectProgram_controllerAt (pc := 76) rfl)
          hresumedPc]
        rw [if_neg (by simp [hresumedPhase])]
        rw [show 3 + foldFuel = (2 + foldFuel) + 1 by omega]
        rw [run_decrement_instruction (value := 0)
          (selectiveAddressSelectProgram_controllerAt (pc := 77) rfl) rfl
          (by simp [NPOracleState.jump, hresumedPhase]) hzeroBits]
        rw [show 2 + foldFuel = (1 + foldFuel) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveAddressSelectProgram_controllerAt (pc := 78) rfl) rfl]
        rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [show 1 + foldFuel = foldFuel + 1 by omega]
        rw [run_copy_instruction (value := (selectiveConst state false).output)
          (selectiveAddressSelectProgram_controllerAt (pc := 40) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, selectiveConst,
              hresumedOutput])
          hconstOutputBits]
        rw [← hfoldFuelEq]
        refine run_selectiveAddressSelectFoldLoop spine
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
  | succ remaining ih =>
      have hcountdownNonzero : machine.registers 19 ≠ 0 := by
        rw [hcountdown]
        omega
      cases hbit : addressCode.testBit index with
      | true =>
          have hwireEq :
              (selectiveAddressSelectWire row start limit addressCode hblock state index) =
                (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit index
                hblock)) := by
            simp only [selectiveAddressSelectWire, selectiveAddressSelectExpr]
            rw [if_pos hbit]
          obtain ⟨unaryFuel, hunaryFuelEq⟩ :
              ∃ fuel, selectiveUnaryRunFuel state (selectiveUnaryEqualsLiterals (n := n) row start
                limit index hblock) = fuel := ⟨_, rfl⟩
          obtain ⟨recFuel, hrecFuel⟩ :
              ∃ fuel,
                selectiveAddressSelectForwardFuel row start limit addressCode
                    hblock (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
                      index hblock)).state (index + 1) remaining
                    ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit index
                      hblock)).output :: spine) = fuel := ⟨_, rfl⟩
          have hfuel :
              selectiveAddressSelectForwardFuel row start limit addressCode
                  hblock state index (remaining + 1) spine =
                5 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) := by
            rw [← hunaryFuelEq, ← hrecFuel]
            rw [selectiveAddressSelectForwardFuel, if_pos hbit, hwireEq]
          have hbitsSucc :
              selectiveAddressSelectForwardBits row start limit addressCode
                  hblock state index (remaining + 1) spine =
                max
                  (selectiveUnaryRunBits state (selectiveUnaryEqualsLiterals (n := n) row start
                    limit index hblock)
                    (row.val * rowWidth n bound) start index)
                  (max
                    (natBitLength
                      (selectiveUnaryInput (selectiveStateCode state) (descriptionWidth n bound)
                        (row.val * rowWidth n bound) start limit index))
                    (max
                      (natBitLength
                        (Nat.pair 0 (selectiveWireCode (selectiveCompileExpr state (unaryEqualsExpr
                          (n := n) row start limit index hblock)))))
                      (max (natBitLength (index + 1))
                        (max (natBitLength remaining)
            (max
              (natBitLength
                (selectiveCountCasesSpineCode ((selectiveCompileExpr state (unaryEqualsExpr (n :=
                  n) row start limit index hblock)).output :: spine)))
              (selectiveAddressSelectForwardBits row start limit addressCode
                hblock (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit index
                  hblock)).state (index + 1) remaining
                ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit index
                  hblock)).output :: spine))))))) := by
            rw [selectiveAddressSelectForwardBits, if_pos hbit, hwireEq]
          rw [hbitsSucc] at hbits
          have hcalleeBits := (Nat.le_max_left _ _).trans hbits
          have hbitsOne := (Nat.le_max_right _ _).trans hbits
          have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
          have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
          have hwireBits := (Nat.le_max_left _ _).trans hbitsTwo
          have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
          have hindexBits := (Nat.le_max_left _ _).trans hbitsThree
          have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
          have hremainingBits := (Nat.le_max_left _ _).trans hbitsFour
          have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
          have hnewSpineBits := (Nat.le_max_left _ _).trans hbitsFive
          have hrecBits := (Nat.le_max_right _ _).trans hbitsFive
          have hnewSpineForm :
              selectiveCountCasesSpineCode ((selectiveCompileExpr state (unaryEqualsExpr (n := n)
                row start limit index hblock)).output :: spine) =
                Nat.pair 1
                  (Nat.pair (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
                    index hblock)).output
                    (selectiveCountCasesSpineCode spine)) := rfl
          have honeBits : natBitLength 1 ≤ maximumBits := by
            refine (natBitLength_mono ?_).trans hnewSpineBits
            rw [hnewSpineForm]
            exact Nat.left_le_pair 1 _
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            (natBitLength_mono (Nat.zero_le _)).trans honeBits
          have hspinePairBits :
              natBitLength
                  (Nat.pair (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
                    index hblock)).output
                    (selectiveCountCasesSpineCode spine)) ≤ maximumBits := by
            refine (natBitLength_mono ?_).trans hnewSpineBits
            rw [hnewSpineForm]
            exact Nat.right_le_pair 1 _
          have hstepOrdered :
              selectiveStateOrdered (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start
                limit index hblock)).state :=
            selectiveCompileExpr_ordered state _ hordered
          rw [hfuel, selectiveAddressSelectForwardOutput_succ, hwireEq]
          rw [show 5 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) =
            (4 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 19) rfl) hpc]
          rw [if_neg hcountdownNonzero]
          rw [show 4 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) =
            (3 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_testBit_instruction (value := 1)
            (selectiveAddressSelectProgram_controllerAt (pc := 20) rfl) rfl
            (by simp [NPOracleState.jump, haddress, hbitIndex, hbit]) honeBits]
          rw [show 3 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) =
            (2 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 21) rfl) rfl]
          rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [show 2 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) =
            (1 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_set_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 22) rfl) rfl
            hzeroBits]
          rw [show 1 + (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) =
            (9 + (unaryFuel + (7 + (1 + (6 + recFuel))))) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 23) rfl) rfl]
          simp only [ite_self]
          refine run_selectiveAddressSelectUnaryCall state row start limit
            index hblock hordered maximumBits unaryFuel (1 + (6 + recFuel)) _
            (machine.registers 15) addressCode
            (selectiveCountCasesSpineCode spine) (remaining + 1)
            (machine.registers 28) 0 _ hunaryFuelEq.symm hcalleeBits
            hrequestBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ?_
          · rfl
          · simp [NPOracleState.write, NPOracleState.jump, hremainingReg]
          · simp [NPOracleState.write, NPOracleState.jump, hnext]
          · simp [NPOracleState.write, NPOracleState.jump, hselected]
          · simp [NPOracleState.write, NPOracleState.jump, harity]
          · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
          · simp [NPOracleState.write, NPOracleState.jump, hstart]
          · simp [NPOracleState.write, NPOracleState.jump, hlimit]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump, haddress]
          · simp [NPOracleState.write, NPOracleState.jump, hbitIndex]
          · simp [NPOracleState.write, NPOracleState.jump, hspine]
          · simp [NPOracleState.write, NPOracleState.jump, hcountdown]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · intro resumed hstepPc hstepRemaining hstepNext hstepSelected
              hstepOutput hstepArity hstepRowBase hstepStart hstepLimit _
              hstepAddress hstepBitIndex hstepSpine hstepCountdown _
              hstepPhase
            rw [show 1 + (6 + recFuel) = (6 + recFuel) + 1 by omega]
            rw [run_branchZero_instruction
              (selectiveAddressSelectProgram_controllerAt (pc := 76) rfl) hstepPc]
            rw [if_pos hstepPhase]
            rw [show 6 + recFuel = (5 + recFuel) + 1 by omega]
            rw [run_pair_instruction
              (value :=
                Nat.pair (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit
                  index hblock)).output
                  (selectiveCountCasesSpineCode spine))
              (selectiveAddressSelectProgram_controllerAt (pc := 29) rfl) rfl
              (by
                simp [NPOracleState.jump, hstepOutput,
                  hstepSpine])
              hspinePairBits]
            rw [show 5 + recFuel = (4 + recFuel) + 1 by omega]
            rw [run_set_instruction
              (selectiveAddressSelectProgram_controllerAt (pc := 30) rfl) rfl honeBits]
            rw [show 4 + recFuel = (3 + recFuel) + 1 by omega]
            rw [run_pair_instruction
              (value :=
                selectiveCountCasesSpineCode ((selectiveCompileExpr state (unaryEqualsExpr (n := n)
                  row start limit index hblock)).output :: spine))
              (selectiveAddressSelectProgram_controllerAt (pc := 31) rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump, hnewSpineForm])
              hnewSpineBits]
            rw [show 3 + recFuel = (2 + recFuel) + 1 by omega]
            rw [run_increment_instruction (value := index + 1)
              (selectiveAddressSelectProgram_controllerAt (pc := 32) rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump, hstepBitIndex])
              hindexBits]
            rw [show 2 + recFuel = (1 + recFuel) + 1 by omega]
            rw [run_decrement_instruction (value := remaining)
              (selectiveAddressSelectProgram_controllerAt (pc := 33) rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump, hstepCountdown])
              hremainingBits]
            rw [show 1 + recFuel = recFuel + 1 by omega]
            rw [run_branchZero_instruction
              (selectiveAddressSelectProgram_controllerAt (pc := 34) rfl) rfl]
            simp only [ite_self]
            rw [← hrecFuel]
            refine ih (selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit index
              hblock)).state (index + 1)
              ((selectiveCompileExpr state (unaryEqualsExpr (n := n) row start limit index
                hblock)).output :: spine) hstepOrdered hrecBits _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
              ?_ ?_ ?_ ?_
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepRemaining
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepNext
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepSelected
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepArity
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepRowBase
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepStart
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepLimit
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepAddress
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
      | false =>
          have hwireEq :
              (selectiveAddressSelectWire row start limit addressCode hblock state index) =
                (selectiveConst state false) := by
            simp only [selectiveAddressSelectWire, selectiveAddressSelectExpr]
            rw [if_neg (by simp [hbit])]
            rfl
          obtain ⟨emitFuel, hemitFuelEq⟩ :
              ∃ fuel,
                selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) = fuel := ⟨_, rfl⟩
          obtain ⟨recFuel, hrecFuel⟩ :
              ∃ fuel,
                selectiveAddressSelectForwardFuel row start limit addressCode
                    hblock (selectiveConst state false).state (index + 1) remaining
                    ((selectiveConst state false).output :: spine) = fuel := ⟨_, rfl⟩
          have hfuel :
              selectiveAddressSelectForwardFuel row start limit addressCode
                  hblock state index (remaining + 1) spine =
                8 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) := by
            rw [← hemitFuelEq, ← hrecFuel]
            rw [selectiveAddressSelectForwardFuel,
              if_neg (by simp [hbit]), hwireEq]
          have hbitsSucc :
              selectiveAddressSelectForwardBits row start limit addressCode
                  hblock state index (remaining + 1) spine =
                max
                  (natBitLength
                    (selectiveEmitInput (state.target - state.next) state.next
                      (selectiveSelectedCode state.selected)
                      (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false))))
                  (max
                    (natBitLength
                      (Nat.pair 0 (selectiveWireCode (selectiveConst state false))))
                    (max (natBitLength (index + 1))
                      (max (natBitLength remaining)
                        (max
                          (natBitLength
                            (selectiveCountCasesSpineCode
                              ((selectiveConst state false).output :: spine)))
                          (selectiveAddressSelectForwardBits row start limit
                            addressCode hblock (selectiveConst state false).state (index + 1)
                            remaining
                            ((selectiveConst state false).output :: spine)))))) := by
            rw [selectiveAddressSelectForwardBits,
              if_neg (by simp [hbit]), hwireEq]
          rw [hbitsSucc] at hbits
          have hinputBits := (Nat.le_max_left _ _).trans hbits
          have hbitsOne := (Nat.le_max_right _ _).trans hbits
          have hwireBits := (Nat.le_max_left _ _).trans hbitsOne
          have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
          have hindexBits := (Nat.le_max_left _ _).trans hbitsTwo
          have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
          have hremainingBits := (Nat.le_max_left _ _).trans hbitsThree
          have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
          have hnewSpineBits := (Nat.le_max_left _ _).trans hbitsFour
          have hrecBits := (Nat.le_max_right _ _).trans hbitsFour
          have hnewSpineForm :
              selectiveCountCasesSpineCode ((selectiveConst state false).output :: spine) =
                Nat.pair 1
                  (Nat.pair (selectiveConst state false).output
                    (selectiveCountCasesSpineCode spine)) := rfl
          have honeBits : natBitLength 1 ≤ maximumBits := by
            refine (natBitLength_mono ?_).trans hnewSpineBits
            rw [hnewSpineForm]
            exact Nat.left_le_pair 1 _
          have hzeroBits : natBitLength 0 ≤ maximumBits :=
            (natBitLength_mono (Nat.zero_le _)).trans honeBits
          have hspinePairBits :
              natBitLength
                  (Nat.pair (selectiveConst state false).output
                    (selectiveCountCasesSpineCode spine)) ≤ maximumBits := by
            refine (natBitLength_mono ?_).trans hnewSpineBits
            rw [hnewSpineForm]
            exact Nat.right_le_pair 1 _
          have hnodeCode :
              rawCircuitNodeCode (n := descriptionWidth n bound) (.const false) =
                Nat.pair 0 0 := rfl
          have hemitInput :
              selectiveEmitInput (state.target - state.next) state.next
                  (selectiveSelectedCode state.selected)
                  (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)) =
                Nat.pair (selectiveStateCode state)
                  (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)) := rfl
          have hcodeBits :
              natBitLength (rawCircuitNodeCode (n := descriptionWidth n bound) (.const false)) ≤
                maximumBits := by
            refine (natBitLength_mono ?_).trans hinputBits
            rw [hemitInput]
            exact Nat.right_le_pair _ _
          have hstepOrdered :
              selectiveStateOrdered (selectiveConst state false).state :=
            selectiveState_emit_ordered state (.const false) hordered
          rw [hfuel, selectiveAddressSelectForwardOutput_succ, hwireEq]
          rw [show 8 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (7 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 19) rfl) hpc]
          rw [if_neg hcountdownNonzero]
          rw [show 7 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (6 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_testBit_instruction (value := 0)
            (selectiveAddressSelectProgram_controllerAt (pc := 20) rfl) rfl
            (by simp [NPOracleState.jump, haddress, hbitIndex, hbit])
            hzeroBits]
          rw [show 6 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (5 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 21) rfl) rfl]
          rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
          rw [show 5 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (4 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_set_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 24) rfl) rfl
            hzeroBits]
          rw [show 4 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (3 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_set_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 25) rfl) rfl
            hzeroBits]
          rw [show 3 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (2 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_pair_instruction
            (value := rawCircuitNodeCode (n := descriptionWidth n bound) (.const false))
            (selectiveAddressSelectProgram_controllerAt (pc := 26) rfl) rfl
            (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode])
            hcodeBits]
          rw [show 2 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (1 + (5 + (emitFuel + (7 + (1 + (6 + recFuel)))))) + 1 by omega]
          rw [run_set_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 27) rfl) rfl
            hzeroBits]
          rw [show 1 + (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) =
            (5 + (emitFuel + (7 + (1 + (6 + recFuel))))) + 1 by omega]
          rw [run_branchZero_instruction
            (selectiveAddressSelectProgram_controllerAt (pc := 28) rfl) rfl]
          simp only [ite_self]
          refine run_selectiveAddressSelectEmitCall state (.const false)
            hordered maximumBits emitFuel (1 + (6 + recFuel)) _ (descriptionWidth n bound)
            (row.val * rowWidth n bound) start limit (machine.registers 15)
            addressCode index (selectiveCountCasesSpineCode spine)
            (remaining + 1) (machine.registers 28) 0 _ hemitFuelEq.symm
            hinputBits hwireBits ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ?_ ?_
          · rfl
          · simp [NPOracleState.write, NPOracleState.jump, hremainingReg]
          · simp [NPOracleState.write, NPOracleState.jump, hnext]
          · simp [NPOracleState.write, NPOracleState.jump, hselected]
          · simp [NPOracleState.write, NPOracleState.jump, hnodeCode]
          · simp [NPOracleState.write, NPOracleState.jump, harity]
          · simp [NPOracleState.write, NPOracleState.jump, hrowBase]
          · simp [NPOracleState.write, NPOracleState.jump, hstart]
          · simp [NPOracleState.write, NPOracleState.jump, hlimit]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump, haddress]
          · simp [NPOracleState.write, NPOracleState.jump, hbitIndex]
          · simp [NPOracleState.write, NPOracleState.jump, hspine]
          · simp [NPOracleState.write, NPOracleState.jump, hcountdown]
          · simp [NPOracleState.write, NPOracleState.jump]
          · simp [NPOracleState.write, NPOracleState.jump]
          · intro resumed hstepPc _ hstepRemaining hstepNext hstepSelected
              hstepOutput hstepArity hstepRowBase hstepStart hstepLimit _
              hstepAddress hstepBitIndex hstepSpine hstepCountdown _
              hstepPhase
            rw [show 1 + (6 + recFuel) = (6 + recFuel) + 1 by omega]
            rw [run_branchZero_instruction
              (selectiveAddressSelectProgram_controllerAt (pc := 76) rfl) hstepPc]
            rw [if_pos hstepPhase]
            rw [show 6 + recFuel = (5 + recFuel) + 1 by omega]
            rw [run_pair_instruction
              (value :=
                Nat.pair (selectiveConst state false).output
                  (selectiveCountCasesSpineCode spine))
              (selectiveAddressSelectProgram_controllerAt (pc := 29) rfl) rfl
              (by
                simp [NPOracleState.jump, selectiveConst,
                  hstepOutput, hstepSpine])
              hspinePairBits]
            rw [show 5 + recFuel = (4 + recFuel) + 1 by omega]
            rw [run_set_instruction
              (selectiveAddressSelectProgram_controllerAt (pc := 30) rfl) rfl honeBits]
            rw [show 4 + recFuel = (3 + recFuel) + 1 by omega]
            rw [run_pair_instruction
              (value :=
                selectiveCountCasesSpineCode ((selectiveConst state false).output :: spine))
              (selectiveAddressSelectProgram_controllerAt (pc := 31) rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump, hnewSpineForm])
              hnewSpineBits]
            rw [show 3 + recFuel = (2 + recFuel) + 1 by omega]
            rw [run_increment_instruction (value := index + 1)
              (selectiveAddressSelectProgram_controllerAt (pc := 32) rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump, hstepBitIndex])
              hindexBits]
            rw [show 2 + recFuel = (1 + recFuel) + 1 by omega]
            rw [run_decrement_instruction (value := remaining)
              (selectiveAddressSelectProgram_controllerAt (pc := 33) rfl) rfl
              (by simp [NPOracleState.write, NPOracleState.jump, hstepCountdown])
              hremainingBits]
            rw [show 1 + recFuel = recFuel + 1 by omega]
            rw [run_branchZero_instruction
              (selectiveAddressSelectProgram_controllerAt (pc := 34) rfl) rfl]
            simp only [ite_self]
            rw [← hrecFuel]
            refine ih (selectiveConst state false).state (index + 1)
              ((selectiveConst state false).output :: spine) hstepOrdered hrecBits _ rfl ?_ ?_ ?_
                ?_ ?_ ?_ ?_
              ?_ ?_ ?_ ?_
            · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst] using
                hstepRemaining
            · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst] using
                hstepNext
            · simpa [NPOracleState.write, NPOracleState.jump, selectiveConst] using
                hstepSelected
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepArity
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepRowBase
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepStart
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepLimit
            · simpa [NPOracleState.write, NPOracleState.jump] using hstepAddress
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]
            · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 6. The level premise, discharged -/

private theorem selectiveAddressSelectForwardOutput_nil_spine {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound))
    (index remaining : ℕ) :
    selectiveAddressSelectForwardOutput row start limit addressCode hblock
        state index remaining [] =
      selectiveCompileExpr state
        (BoolExpr.any
          (selectiveAddressSelectExprs row start limit addressCode hblock index
            remaining)) := by
  rw [selectiveCompileExpr_any_eq_fold]
  simp only [selectiveAddressSelectForwardOutput, List.append_nil]

/-- Interpreter fuel of one whole address selection. -/
def selectiveAddressSelectRunFuel {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (width : ℕ) : ℕ :=
  19 +
    selectiveAddressSelectForwardFuel row start limit addressCode hblock state
      0 width []

/-- Register-width envelope of one whole address selection. -/
def selectiveAddressSelectRunBits {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (state : SelectiveState (descriptionWidth n bound)) (width : ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveAddressSelectInput (selectiveStateCode state)
        (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
        width addressCode))
    (selectiveAddressSelectForwardBits row start limit addressCode hblock state
      0 width [])

/-- **The address selector's run.**  The `195`-instruction stream started on
its own ABI frame, at any entry registers, returns exactly the compiler wire
the source compiler produces for the scheduled disjunction. -/
theorem run_selectiveAddressSelectProgram {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit width addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveAddressSelectInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
          width addressCode) :
    runNPOracleProgram selectiveAddressSelectProgram
        (selectiveAddressSelectRunBits row start limit addressCode hblock state
          width)
        (selectiveAddressSelectRunFuel row start limit addressCode hblock state
          width) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (BoolExpr.any
              (selectiveAddressSelectExprs row start limit addressCode hblock 0
                width)))) := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hrequestBits :
      natBitLength
          (selectiveAddressSelectInput (selectiveStateCode state)
            (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
            width addressCode) ≤
        selectiveAddressSelectRunBits row start limit addressCode hblock state
          width :=
    Nat.le_max_left _ _
  have hforwardBits :
      selectiveAddressSelectForwardBits row start limit addressCode hblock
          state 0 width [] ≤
        selectiveAddressSelectRunBits row start limit addressCode hblock state
          width :=
    Nat.le_max_right _ _
  have hflat := hrequestBits
  simp only [selectiveAddressSelectInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have hrowBaseBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hstartBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hlimitBits := natBitLength_pair_left hfour
  have hfive := natBitLength_pair_right hfour
  have hwidthBits := natBitLength_pair_left hfive
  have haddressBits := natBitLength_pair_right hfive
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left hnextSelectedBits
  have hselectedBits := natBitLength_pair_right hnextSelectedBits
  have hzeroBits :
      natBitLength 0 ≤
        selectiveAddressSelectRunBits row start limit addressCode hblock state
          width :=
    (natBitLength_mono (Nat.zero_le _)).trans hwidthBits
  rw [← selectiveAddressSelectForwardOutput_nil_spine]
  rw [selectiveAddressSelectRunFuel]
  rw [show 19 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (18 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveAddressSelectProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, selectiveAddressSelectInput])
    hstateBits]
  rw [show 18 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (17 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair (descriptionWidth n bound) <|
      Nat.pair (row.val * rowWidth n bound) <|
        Nat.pair start <|
          Nat.pair limit (Nat.pair width addressCode))
    (selectiveAddressSelectProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveAddressSelectInput])
    hone]
  rw [show 17 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (16 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveAddressSelectProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 16 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (15 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair state.next (selectiveSelectedCode
    state.selected))
    (selectiveAddressSelectProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hnextSelectedBits]
  rw [show 15 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (14 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveAddressSelectProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hnextBits]
  rw [show 14 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (13 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveSelectedCode state.selected)
    (selectiveAddressSelectProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hselectedBits]
  rw [show 13 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (12 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairLeft_instruction (value := descriptionWidth n bound)
    (selectiveAddressSelectProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    harityBits]
  rw [show 12 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (11 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair (row.val * rowWidth n bound) <|
      Nat.pair start (Nat.pair limit (Nat.pair width addressCode)))
    (selectiveAddressSelectProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    htwo]
  rw [show 11 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (10 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []))
      + 1 by omega]
  rw [run_unpairLeft_instruction (value := row.val * rowWidth n bound)
    (selectiveAddressSelectProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hrowBaseBits]
  rw [show 10 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (9 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair start (Nat.pair limit (Nat.pair width
    addressCode)))
    (selectiveAddressSelectProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hthree]
  rw [show 9 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (8 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairLeft_instruction (value := start)
    (selectiveAddressSelectProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hstartBits]
  rw [show 8 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (7 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair limit (Nat.pair width addressCode))
    (selectiveAddressSelectProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hfour]
  rw [show 7 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (6 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairLeft_instruction (value := limit)
    (selectiveAddressSelectProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hlimitBits]
  rw [show 6 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (5 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair width addressCode)
    (selectiveAddressSelectProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hfive]
  rw [show 5 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (4 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (selectiveAddressSelectProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    hwidthBits]
  rw [show 4 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (3 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_unpairRight_instruction (value := addressCode)
    (selectiveAddressSelectProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    haddressBits]
  rw [show 3 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (2 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_set_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 16) rfl) rfl hzeroBits]
  rw [show 2 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (1 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width [])) +
      1 by omega]
  rw [run_set_instruction
    (selectiveAddressSelectProgram_controllerAt (pc := 17) rfl) rfl hzeroBits]
  rw [show 1 + (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width
    []) =
    (selectiveAddressSelectForwardFuel row start limit addressCode hblock state 0 width []) + 1 by
      omega]
  rw [run_copy_instruction (value := width)
    (selectiveAddressSelectProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  refine run_selectiveAddressSelectForwardLoop row start limit addressCode
    hblock width state 0 [] _ hordered hforwardBits _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump,
      selectiveCountCasesSpineCode]

/-! ### The constant address-selection expression -/

private theorem selectiveAddressSelectExprs_eq_ofFn {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit addressCode : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) (remaining : ℕ) :
    ∀ offset : ℕ,
      selectiveAddressSelectExprs (n := n) row start limit addressCode hblock
          offset remaining =
        List.ofFn fun index : Fin remaining =>
          selectiveAddressSelectExpr (n := n) row start limit addressCode
            (offset + index.val) hblock := by
  induction remaining with
  | zero => intro offset; rfl
  | succ remaining ih =>
      intro offset
      rw [selectiveAddressSelectExprs, ih (offset + 1)]
      simp only [List.ofFn_succ, Nat.add_zero, Fin.val_succ, Fin.val_zero]
      refine congrArg₂ List.cons rfl (congrArg List.ofFn (funext ?_))
      intro index
      congr 1
      omega

/-- The controller's disjunct schedule is exactly the source compiler's
constant address selection. -/
theorem boolExpr_any_selectiveAddressSelectExprs {n bound : ℕ}
    (row : Fin (bound + 1)) (address : BitInput n)
    (hblock :
      6 + boundedCircuitFieldLimit n bound ≤ rowWidth n bound) :
    BoolExpr.any
        (selectiveAddressSelectExprs (n := n) row 6
          (boundedCircuitFieldLimit n bound) (encodeBitInput address) hblock 0
          n) =
      constantAddressSelectionExpr row address := by
  rw [selectiveAddressSelectExprs_eq_ofFn]
  refine congrArg BoolExpr.any (congrArg List.ofFn (funext ?_))
  intro index
  have hbit : (encodeBitInput address).testBit index.val = address index := by
    rw [encodeBitInput_eq_ofBits]
    exact Nat.testBit_ofBits_lt address index.val index.isLt
  simp only [selectiveAddressSelectExpr, Nat.zero_add, hbit]
  rfl

/-- **Level premise.**  The address selector compiles one constant address
selection at its own ABI frame. -/
structure SelectiveAddressSelectRunner (width bound : ℕ) where
  bits : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    BitInput width → ℕ
  fuel : SelectiveState (descriptionWidth width bound) → Fin (bound + 1) →
    BitInput width → ℕ
  executes : ∀ (state : SelectiveState (descriptionWidth width bound))
      (row : Fin (bound + 1)) (address : BitInput width),
      selectiveStateOrdered state →
    ∀ entry : NPOracleState, entry.pc = 0 →
    entry.registers 0 =
      selectiveAddressSelectInput (selectiveStateCode state)
        (descriptionWidth width bound) (row.val * rowWidth width bound) 6
        (boundedCircuitFieldLimit width bound) width
        (encodeBitInput address) →
    runNPOracleProgram selectiveAddressSelectProgram (bits state row address)
        (fuel state row address) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (constantAddressSelectionExpr row address)))

/-- **Level premise, discharged.**  The address selector's run at its own ABI
frame, packaged in the runner shape the callers one level up consume.  Nothing
on this level is left as a premise. -/
def selectiveAddressSelectRunner (width bound : ℕ)
    (hblock :
      6 + boundedCircuitFieldLimit width bound ≤ rowWidth width bound) :
    SelectiveAddressSelectRunner width bound where
  bits state row address :=
    selectiveAddressSelectRunBits row 6 (boundedCircuitFieldLimit width bound)
      (encodeBitInput address) hblock state width
  fuel state row address :=
    selectiveAddressSelectRunFuel row 6 (boundedCircuitFieldLimit width bound)
      (encodeBitInput address) hblock state width
  executes := by
    intro state row address hordered entry hentryPc hentryInput
    rw [← boolExpr_any_selectiveAddressSelectExprs row address hblock]
    exact run_selectiveAddressSelectProgram state row 6
      (boundedCircuitFieldLimit width bound) width (encodeBitInput address)
      hblock hordered entry hentryPc hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
