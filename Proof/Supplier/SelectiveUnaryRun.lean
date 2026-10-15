import Proof.Supplier.SelectiveCountCasesRun

/-!
# The unary-equality compiler's run

`selectiveUnaryProgram` is the `97`-instruction stream sitting at the very
bottom of the nested structural compiler's tower: a straight-line controller of
`79` instructions with one relocated callee, the `18`-instruction append
transition.  Every other selective level reaches it, directly or through the
field/address selectors, so its run is the only level below the fixed-count
grammar compiler and the verifier-row scheduler that closes outright.

The controller compiles `unaryEqualsExpr`, i.e. the conjunction
`BoolExpr.all` of one literal per unary offset.  Its forward pass emits one
input node per offset (and one negation whenever the offset has left the unary
prefix) and retains each conjunct's output on a private reverse spine; its
reverse pass then rebuilds the source compiler's right-associated conjunction
from the explicit `true` base case, one append per spine entry.  Both passes
are proved here, so this module leaves no premise behind.
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

/-! ## 1. The controller's two passes, at the typed level

The source compiler folds a conjunction to the right, so the outermost `and`
node is appended last and its left child is the first conjunct.  The controller
instead compiles every conjunct first, retains their outputs on a reverse
spine, and only then emits the conjunctions from the innermost outwards.  Both
orders append exactly the same nodes in exactly the same order; §1 proves that.
-/

/-- The forward pass: one compiled conjunct per list entry, in the ascending
order the controller visits them. -/
def selectiveUnaryHeads {n : ℕ} :
    SelectiveState n → List (BoolExpr n) → SelectiveWireList n
  | state, [] => { state := state, values := [] }
  | state, expression :: rest =>
      let head := selectiveCompileExpr state expression
      let tail := selectiveUnaryHeads head.state rest
      { state := tail.state
        values := head.output :: tail.values }

/-- The reverse pass: one conjunction per retained conjunct output. -/
def selectiveUnaryFold {n : ℕ} :
    SelectiveState n → ℕ → List ℕ → SelectiveWire n
  | state, accumulated, [] => { state := state, output := accumulated }
  | state, accumulated, value :: rest =>
      let combined := selectiveAnd state value accumulated
      selectiveUnaryFold combined.state combined.output rest

theorem selectiveUnaryFold_concat {n : ℕ} (values : List ℕ)
    (state : SelectiveState n) (accumulated value : ℕ) :
    selectiveUnaryFold state accumulated (values ++ [value]) =
      selectiveAnd (selectiveUnaryFold state accumulated values).state value
        (selectiveUnaryFold state accumulated values).output := by
  induction values generalizing state accumulated with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.cons_append, selectiveUnaryFold]
      exact ih _ _

theorem selectiveUnaryHeads_ordered {n : ℕ} (expressions : List (BoolExpr n))
    (state : SelectiveState n) (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered (selectiveUnaryHeads state expressions).state := by
  induction expressions generalizing state with
  | nil => exact hordered
  | cons expression rest ih =>
      exact ih _ (selectiveCompileExpr_ordered state expression hordered)

/-- **The controller's scheduling identity.**  The source compiler's
right-associated conjunction is exactly the forward conjunct pass followed by
the reverse fold over the retained spine. -/
theorem selectiveCompileExpr_all_eq_fold {n : ℕ}
    (expressions : List (BoolExpr n)) (state : SelectiveState n) :
    selectiveCompileExpr state (BoolExpr.all expressions) =
      selectiveUnaryFold
        (selectiveConst (selectiveUnaryHeads state expressions).state
          true).state
        (selectiveConst (selectiveUnaryHeads state expressions).state
          true).output
        (selectiveUnaryHeads state expressions).values.reverse := by
  induction expressions generalizing state with
  | nil => rfl
  | cons expression rest ih =>
      simp only [BoolExpr.all, selectiveCompileExpr, selectiveUnaryHeads,
        List.reverse_cons]
      rw [selectiveUnaryFold_concat]
      rw [ih]

/-! ## 2. Decoding the fixed 97-instruction stream -/

private theorem selectiveUnaryProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup : (selectiveUnaryControllerProgram 79)[pc]? = some instruction) :
    selectiveUnaryProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveUnaryControllerProgram 79).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveUnaryControllerProgram_length] at hpc
  simp only [selectiveUnaryProgram]
  rw [List.getElem?_append_left (by
    simp only [selectiveUnaryControllerProgram_length]
    omega)]
  exact hlookup

/-! ## 3. The single shared call frame

All four append sites of this controller — the input node, the negation, the
`true` base case and every conjunction — reach the relocated append through the
same physical block at `58`.  The block builds the callee's request from the
live state registers, runs the callee, and unpacks the returned wire back into
those same registers; it then falls through to the phase dispatcher at `70`.
Every later trace in this module goes through this one lemma. -/

-- Five request-building steps around the relocated append, then seven steps
-- unpacking the returned wire back into the controller's live registers.
private theorem run_selectiveUnaryEmitCall {n : ℕ}
    (state : SelectiveState n) (node : BooleanNode n)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (arity index spine countdown unaryLeft accumulated phase : ℕ)
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
    (hpc : machine.pc = 58)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (hnode : machine.registers 21 = rawCircuitNodeCode node)
    (harity : machine.registers 8 = arity)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = spine)
    (hcountdown : machine.registers 18 = countdown)
    (hunaryLeft : machine.registers 19 = unaryLeft)
    (haccumulated : machine.registers 27 = accumulated)
    (hphase : machine.registers 30 = phase)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 70 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 2 = selectiveStateCode (state.emit node).state →
      resumed.registers 4 =
        (state.emit node).state.target - (state.emit node).state.next →
      resumed.registers 6 = (state.emit node).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (state.emit node).state.selected →
      resumed.registers 25 = (state.emit node).output →
      resumed.registers 8 = arity →
      resumed.registers 16 = index →
      resumed.registers 17 = spine →
      resumed.registers 18 = countdown →
      resumed.registers 19 = unaryLeft →
      resumed.registers 27 = accumulated →
      resumed.registers 30 = phase →
      runNPOracleProgram selectiveUnaryProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUnaryProgram maximumBits
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
    (selectiveUnaryProgram_controllerAt (pc := 58) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [show 4 + (emitFuel + (7 + extraFuel)) =
    (3 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveUnaryProgram_controllerAt (pc := 59) rfl) rfl
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
    (selectiveUnaryProgram_controllerAt (pc := 60) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [show 2 + (emitFuel + (7 + extraFuel)) =
    (1 + (emitFuel + (7 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 61) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (7 + extraFuel)) =
    (emitFuel + (7 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUnaryProgram_controllerAt (pc := 62) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveUnaryProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
      (selectiveUnaryProgram_controllerAt (pc := 63) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveUnaryProgram_controllerAt (pc := 64) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedStateBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveUnaryProgram_controllerAt (pc := 65) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hemittedOutputBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        (state.emit node).state.target - (state.emit node).state.next)
      (selectiveUnaryProgram_controllerAt (pc := 66) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedRemainingBits]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveUnaryProgram_controllerAt (pc := 67) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          hstateForm (state.emit node).state])
      hemittedTailBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveUnaryProgram_controllerAt (pc := 68) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedNextBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveUnaryProgram_controllerAt (pc := 69) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hemittedSelectedBits]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, harity,
        hindex, hspine, hcountdown, hunaryLeft, haccumulated, hphase]

/-! ## 4. The reverse conjunction fold

Interpreter resources on this level are data dependent, so the fold's clock and
register-width envelope are defined by the same recursion as its output.  The
spine encoding is the one already fixed by the outermost controller. -/

/-- Interpreter fuel of the reverse fold: eleven controller steps, one relocated
append, and an eight-step phase dispatch per retained conjunct. -/
def selectiveUnaryFoldFuel {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      11 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              (8 +
                selectiveUnaryFoldFuel
                  (selectiveAnd state value accumulated).state
                  (selectiveAnd state value accumulated).output rest))))

/-- Largest value the reverse fold ever writes. -/
def selectiveUnaryFoldWorkBound {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | state, accumulated, [] => Nat.pair (selectiveStateCode state) accumulated
  | state, accumulated, value :: rest =>
      max (selectiveCountCasesSpineCode (value :: rest)) <|
        max
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.and value accumulated))) <|
          max
            (Nat.pair 0
              (selectiveWireCode (selectiveAnd state value accumulated))) <|
            selectiveUnaryFoldWorkBound
              (selectiveAnd state value accumulated).state
              (selectiveAnd state value accumulated).output rest

-- One fold iteration is eleven controller steps and an eight-step phase
-- dispatch around the shared call frame of §3.
private theorem run_selectiveUnaryFoldStep {n : ℕ}
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
            (rawCircuitNodeCode (n := n) (.and value accumulated))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode (selectiveAnd state value accumulated))) ≤
        maximumBits)
    (hpc : machine.pc = 44)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hspine :
      machine.registers 17 = selectiveCountCasesSpineCode (value :: rest))
    (haccumulated : machine.registers 27 = accumulated)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 44 →
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
      resumed.registers 17 = selectiveCountCasesSpineCode rest →
      resumed.registers 27 = (selectiveAnd state value accumulated).output →
      runNPOracleProgram selectiveUnaryProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUnaryProgram maximumBits
        (11 + (5 + (emitFuel + (7 + (8 + extraFuel))))) machine =
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
  have hwireForm :
      selectiveWireCode (selectiveAnd state value accumulated) =
        Nat.pair
          (selectiveStateCode (selectiveAnd state value accumulated).state)
          (selectiveAnd state value accumulated).output := rfl
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
  have htwoBits : natBitLength 2 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hthreeBits
  have honeBits : natBitLength 1 ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hthreeBits
  have houtputWireBits :
      natBitLength (selectiveWireCode (selectiveAnd state value accumulated)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 0 _)).trans hwireBits
  have hnextOutputBits :
      natBitLength (selectiveAnd state value accumulated).output ≤
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
    (selectiveUnaryProgram_controllerAt (pc := 44) rfl) hpc]
  rw [if_neg hspineNonzero]
  rw [show 10 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (9 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair value (selectiveCountCasesSpineCode rest))
    (selectiveUnaryProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.jump, hspine, hspineForm]) hconsBits]
  rw [show 9 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (8 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_unpairLeft_instruction (value := value)
    (selectiveUnaryProgram_controllerAt (pc := 46) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 8 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (7 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_unpairRight_instruction (value := selectiveCountCasesSpineCode rest)
    (selectiveUnaryProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
  rw [show 7 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (6 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_add_instruction (value := n + value)
    (selectiveUnaryProgram_controllerAt (pc := 48) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hleftChildBits]
  rw [show 6 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (5 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_add_instruction (value := n + accumulated)
    (selectiveUnaryProgram_controllerAt (pc := 49) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, haccumulated])
    hrightChildBits]
  rw [show 5 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (4 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + value) (n + accumulated))
    (selectiveUnaryProgram_controllerAt (pc := 50) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 4 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (3 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 51) rfl) rfl hthreeBits]
  rw [show 3 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (2 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.and value accumulated))
    (selectiveUnaryProgram_controllerAt (pc := 52) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 2 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (1 + (5 + (emitFuel + (7 + (8 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 53) rfl) rfl hthreeBits]
  rw [show 1 + (5 + (emitFuel + (7 + (8 + extraFuel)))) =
    (5 + (emitFuel + (7 + (8 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUnaryProgram_controllerAt (pc := 54) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveUnaryEmitCall state (.and value accumulated) hordered
    maximumBits emitFuel (8 + extraFuel) finalOutput n (machine.registers 16)
    (selectiveCountCasesSpineCode rest) (machine.registers 18)
    (machine.registers 19) (n + accumulated) 3 _ hemitFuel hinputBits hwireBits
    rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · intro resumed hresumedPc hresumedWire _ hresumedRemaining hresumedNext
      hresumedSelected hresumedOutput hresumedArity _ hresumedSpine _ _ _
      hresumedPhase
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 70) rfl) hresumedPc]
    rw [if_neg (by simp [hresumedPhase])]
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := 2)
      (selectiveUnaryProgram_controllerAt (pc := 71) rfl) rfl
      (by simp [NPOracleState.jump, hresumedPhase]) htwoBits]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 72) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := 1)
      (selectiveUnaryProgram_controllerAt (pc := 73) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) honeBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 74) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 75) rfl) rfl]
    simp only [ite_self]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_copy_instruction
      (value := (selectiveAnd state value accumulated).output)
      (selectiveUnaryProgram_controllerAt (pc := 55) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, selectiveAnd,
          hresumedOutput])
      hnextOutputBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 56) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveAnd] using
        hresumedWire
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveAnd] using
        hresumedRemaining
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveAnd] using
        hresumedNext
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveAnd] using
        hresumedSelected
    · simpa [NPOracleState.write, NPOracleState.jump] using hresumedArity
    · simpa [NPOracleState.write, NPOracleState.jump] using hresumedSpine
    · simp [NPOracleState.write, NPOracleState.jump]

-- The fold is one induction on the retained spine.
private theorem run_selectiveUnaryFoldLoop {n : ℕ}
    (values : List ℕ) (state : SelectiveState n) (accumulated : ℕ)
    (hordered : selectiveStateOrdered state) (maximumBits : ℕ)
    (hbits :
      natBitLength (selectiveUnaryFoldWorkBound state accumulated values) ≤
        maximumBits)
    (machine : NPOracleState) (hpc : machine.pc = 44)
    (hwire :
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated)
    (hremaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hspine : machine.registers 17 = selectiveCountCasesSpineCode values)
    (haccumulated : machine.registers 27 = accumulated) :
    runNPOracleProgram selectiveUnaryProgram maximumBits
        (selectiveUnaryFoldFuel state accumulated values) machine =
      some
        (selectiveWireCode (selectiveUnaryFold state accumulated values)) := by
  induction values generalizing state accumulated machine with
  | nil =>
      have hfuel :
          selectiveUnaryFoldFuel state accumulated ([] : List ℕ) =
            (0 + 1) + 1 := rfl
      have hfoldNil :
          selectiveWireCode
              (selectiveUnaryFold state accumulated ([] : List ℕ)) =
            Nat.pair (selectiveStateCode state) accumulated := rfl
      rw [hfuel]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 44) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      refine run_halt_instruction (fuel := 0)
        (selectiveUnaryProgram_controllerAt (pc := 57) rfl) rfl ?_ ?_
      · rw [hfoldNil]
        exact hwire
      · rw [hfoldNil]
        exact hbits
  | cons value rest ih =>
      have hfuel :
          selectiveUnaryFoldFuel state accumulated (value :: rest) =
            11 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    (8 +
                      selectiveUnaryFoldFuel
                        (selectiveAnd state value accumulated).state
                        (selectiveAnd state value accumulated).output
                        rest)))) := rfl
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
      refine run_selectiveUnaryFoldStep state accumulated value rest hordered
        maximumBits _ _ _ machine rfl hspineBits hinputBits hwireBits hpc
        hremaining hnext hselected harity hspine haccumulated ?_
      intro resumed hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedSpine hresumedAccumulated
      exact ih _ _
        (selectiveState_emit_ordered state (.and value accumulated) hordered)
        hrecBits _ hresumedPc hresumedWire hresumedRemaining hresumedNext
        hresumedSelected hresumedArity hresumedSpine hresumedAccumulated

/-! ## 5. The forward literal pass

Each conjunct of a unary equality test is one description input, negated exactly
when the offset has left the unary prefix.  The controller derives that choice
from a single countdown register, so the conjunct list it walks is fixed by the
starting description index and the tested value alone. -/

/-- One conjunct of a unary equality test: a description input, negated when the
flag is `false`. -/
def selectiveUnaryConjunct {n : ℕ} (literal : Fin n × Bool) : BoolExpr n :=
  if literal.2 then .input literal.1 else .not (.input literal.1)

/-- The conjunct list the controller walks from one starting description index
and one tested value: consecutive indices, positive exactly while the unary
countdown is nonzero. -/
inductive SelectiveUnaryLiteralsFrom {n : ℕ} :
    ℕ → ℕ → List (Fin n × Bool) → Prop
  | nil (index value : ℕ) : SelectiveUnaryLiteralsFrom index value []
  | positive {index value : ℕ} {source : Fin n} {rest : List (Fin n × Bool)}
      (hsource : source.val = index) (hvalue : value ≠ 0)
      (hrest : SelectiveUnaryLiteralsFrom (index + 1) (value - 1) rest) :
      SelectiveUnaryLiteralsFrom index value ((source, true) :: rest)
  | negative {index : ℕ} {source : Fin n} {rest : List (Fin n × Bool)}
      (hsource : source.val = index)
      (hrest : SelectiveUnaryLiteralsFrom (index + 1) 0 rest) :
      SelectiveUnaryLiteralsFrom index 0 ((source, false) :: rest)

/-- Interpreter fuel of the whole controller from the conjunct loop head. -/
def selectiveUnaryForwardFuel {n : ℕ} :
    SelectiveState n → List (Fin n × Bool) → List ℕ → ℕ
  | state, [], spine =>
      1 +
        (5 +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                (6 +
                  selectiveUnaryFoldFuel (selectiveConst state true).state
                    (selectiveConst state true).output spine)))))
  | state, literal :: rest, spine =>
      if literal.2 then
        5 +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                (10 +
                  selectiveUnaryForwardFuel (selectiveInput state literal.1).state
                    rest
                    ((selectiveInput state literal.1).output :: spine)))))
      else
        5 +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                (7 +
                  (5 +
                    (selectiveEmitFuel
                        ((selectiveInput state literal.1).state.target -
                          (selectiveInput state literal.1).state.next)
                        (selectiveSelectedCode
                          (selectiveInput state literal.1).state.selected) +
                      (7 +
                        (10 +
                          selectiveUnaryForwardFuel
                            (selectiveNot (selectiveInput state literal.1).state
                              (selectiveInput state literal.1).output).state rest
                            ((selectiveNot (selectiveInput state literal.1).state
                                (selectiveInput state literal.1).output).output ::
                              spine)))))))))

/-- Largest value the whole controller writes from the conjunct loop head, apart
from the three loop counters, which are bounded separately. -/
def selectiveUnaryForwardWorkBound {n : ℕ} :
    SelectiveState n → List (Fin n × Bool) → List ℕ → ℕ
  | state, [], spine =>
      max 2 <|
        max
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.const true))) <|
          max (Nat.pair 0 (selectiveWireCode (selectiveConst state true))) <|
            selectiveUnaryFoldWorkBound (selectiveConst state true).state
              (selectiveConst state true).output spine
  | state, literal :: rest, spine =>
      if literal.2 then
        max
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.input literal.1))) <|
          max
            (Nat.pair 0 (selectiveWireCode (selectiveInput state literal.1))) <|
            max
              (selectiveCountCasesSpineCode
                ((selectiveInput state literal.1).output :: spine)) <|
              selectiveUnaryForwardWorkBound
                (selectiveInput state literal.1).state rest
                ((selectiveInput state literal.1).output :: spine)
      else
        max
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.input literal.1))) <|
          max
            (Nat.pair 0 (selectiveWireCode (selectiveInput state literal.1))) <|
            max
              (selectiveEmitInput
                ((selectiveInput state literal.1).state.target -
                  (selectiveInput state literal.1).state.next)
                (selectiveInput state literal.1).state.next
                (selectiveSelectedCode
                  (selectiveInput state literal.1).state.selected)
                (rawCircuitNodeCode (n := n)
                  (.not (selectiveInput state literal.1).output))) <|
              max
                (Nat.pair 0
                  (selectiveWireCode
                    (selectiveNot (selectiveInput state literal.1).state
                      (selectiveInput state literal.1).output))) <|
                max
                  (selectiveCountCasesSpineCode
                    ((selectiveNot (selectiveInput state literal.1).state
                        (selectiveInput state literal.1).output).output ::
                      spine)) <|
                  selectiveUnaryForwardWorkBound
                    (selectiveNot (selectiveInput state literal.1).state
                      (selectiveInput state literal.1).output).state rest
                    ((selectiveNot (selectiveInput state literal.1).state
                        (selectiveInput state literal.1).output).output :: spine)

-- A positive conjunct: five controller steps into the shared call frame, then a
-- ten-step tail that conses the emitted wire and advances all three counters.
private theorem run_selectiveUnaryPositiveStep {n : ℕ}
    (state : SelectiveState n) (source : Fin n) (index value remaining : ℕ)
    (spine : List ℕ) (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hsource : source.val = index)
    (hvalueNonzero : value ≠ 0) (hremainingNonzero : remaining ≠ 0)
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.input source))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0 (selectiveWireCode (selectiveInput state source))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveInput state source).output :: spine)) ≤
        maximumBits)
    (hvalueBits : natBitLength value ≤ maximumBits)
    (hremainingBits : natBitLength remaining ≤ maximumBits)
    (hindexBits : natBitLength (index + 1) ≤ maximumBits)
    (hpc : machine.pc = 18)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = selectiveCountCasesSpineCode spine)
    (hcountdown : machine.registers 18 = remaining)
    (hunaryLeft : machine.registers 19 = value)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 =
        (selectiveInput state source).state.target -
          (selectiveInput state source).state.next →
      resumed.registers 6 = (selectiveInput state source).state.next →
      resumed.registers 7 =
        selectiveSelectedCode (selectiveInput state source).state.selected →
      resumed.registers 8 = n →
      resumed.registers 16 = index + 1 →
      resumed.registers 17 =
        selectiveCountCasesSpineCode
          ((selectiveInput state source).output :: spine) →
      resumed.registers 18 = remaining - 1 →
      resumed.registers 19 = value - 1 →
      runNPOracleProgram selectiveUnaryProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUnaryProgram maximumBits
        (5 + (5 + (emitFuel + (7 + (10 + extraFuel))))) machine =
      some finalOutput := by
  have hnodeCode :
      rawCircuitNodeCode (n := n) (.input source) =
        Nat.pair 1 source.val := rfl
  have hemitInput :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.input source)) =
        Nat.pair (selectiveStateCode state)
          (rawCircuitNodeCode (n := n) (.input source)) := rfl
  have hspineForm :
      selectiveCountCasesSpineCode
          ((selectiveInput state source).output :: spine) =
        Nat.pair 1
          (Nat.pair (selectiveInput state source).output
            (selectiveCountCasesSpineCode spine)) := rfl
  have hcodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.input source)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hinputBits
    rw [hemitInput]
    exact Nat.right_le_pair _ _
  have honeBits : natBitLength 1 ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.left_le_pair 1 _
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans honeBits
  have hconsBits :
      natBitLength
          (Nat.pair (selectiveInput state source).output
            (selectiveCountCasesSpineCode spine)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  have hvalueLessBits : natBitLength (value - 1) ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hvalueBits
  have hremainingLessBits : natBitLength (remaining - 1) ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hremainingBits
  rw [show 5 + (5 + (emitFuel + (7 + (10 + extraFuel)))) =
    (4 + (5 + (emitFuel + (7 + (10 + extraFuel))))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUnaryProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_neg (by rw [hcountdown]; exact hremainingNonzero)]
  rw [show 4 + (5 + (emitFuel + (7 + (10 + extraFuel)))) =
    (3 + (5 + (emitFuel + (7 + (10 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 19) rfl) rfl honeBits]
  rw [show 3 + (5 + (emitFuel + (7 + (10 + extraFuel)))) =
    (2 + (5 + (emitFuel + (7 + (10 + extraFuel))))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.input source))
    (selectiveUnaryProgram_controllerAt (pc := 20) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hindex, hnodeCode,
        hsource])
    hcodeBits]
  rw [show 2 + (5 + (emitFuel + (7 + (10 + extraFuel)))) =
    (1 + (5 + (emitFuel + (7 + (10 + extraFuel))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 21) rfl) rfl hzeroBits]
  rw [show 1 + (5 + (emitFuel + (7 + (10 + extraFuel)))) =
    (5 + (emitFuel + (7 + (10 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUnaryProgram_controllerAt (pc := 22) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveUnaryEmitCall state (.input source) hordered maximumBits
    emitFuel (10 + extraFuel) finalOutput n index
    (selectiveCountCasesSpineCode spine) remaining value
    (machine.registers 27) 0 _ hemitFuel hinputBits hwireBits rfl ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump, hstateRemaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hindex]
  · simp [NPOracleState.write, NPOracleState.jump, hspine]
  · simp [NPOracleState.write, NPOracleState.jump, hcountdown]
  · simp [NPOracleState.write, NPOracleState.jump, hunaryLeft]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro resumed hresumedPc _ _ hresumedRemaining hresumedNext
      hresumedSelected hresumedOutput hresumedArity hresumedIndex hresumedSpine
      hresumedCountdown hresumedUnary _ hresumedPhase
    rw [show 10 + extraFuel = (9 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 70) rfl) hresumedPc]
    rw [if_pos hresumedPhase]
    rw [show 9 + extraFuel = (8 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 23) rfl) rfl]
    rw [if_neg (by simp [NPOracleState.jump, hresumedUnary, hvalueNonzero])]
    rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := value - 1)
      (selectiveUnaryProgram_controllerAt (pc := 24) rfl) rfl
      (by simp [NPOracleState.jump, hresumedUnary]) hvalueLessBits]
    rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair (selectiveInput state source).output
          (selectiveCountCasesSpineCode spine))
      (selectiveUnaryProgram_controllerAt (pc := 25) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, selectiveInput,
          hresumedOutput, hresumedSpine])
      hconsBits]
    rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_set_instruction
      (selectiveUnaryProgram_controllerAt (pc := 26) rfl) rfl honeBits]
    rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        selectiveCountCasesSpineCode
          ((selectiveInput state source).output :: spine))
      (selectiveUnaryProgram_controllerAt (pc := 27) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hspineForm])
      hspineBits]
    rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 28) rfl) rfl]
    simp only [ite_self]
    rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_increment_instruction (value := index + 1)
      (selectiveUnaryProgram_controllerAt (pc := 76) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hresumedIndex])
      hindexBits]
    rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := remaining - 1)
      (selectiveUnaryProgram_controllerAt (pc := 77) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hresumedCountdown])
      hremainingLessBits]
    rw [show 1 + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 78) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveInput] using
        hresumedRemaining
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveInput] using
        hresumedNext
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveInput] using
        hresumedSelected
    · simpa [NPOracleState.write, NPOracleState.jump] using hresumedArity
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]

-- A negated conjunct: the same five steps into the shared call frame, a

-- frame, and the same ten-step tail.
private theorem run_selectiveUnaryNegativeStep {n : ℕ}
    (state : SelectiveState n) (source : Fin n) (index remaining : ℕ)
    (spine : List ℕ) (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel negateFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hnegateFuel :
      negateFuel =
        selectiveEmitFuel
          ((selectiveInput state source).state.target -
            (selectiveInput state source).state.next)
          (selectiveSelectedCode (selectiveInput state source).state.selected))
    (hsource : source.val = index) (hremainingNonzero : remaining ≠ 0)
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.input source))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0 (selectiveWireCode (selectiveInput state source))) ≤
        maximumBits)
    (hnegateInputBits :
      natBitLength
          (selectiveEmitInput
            ((selectiveInput state source).state.target -
              (selectiveInput state source).state.next)
            (selectiveInput state source).state.next
            (selectiveSelectedCode (selectiveInput state source).state.selected)
            (rawCircuitNodeCode (n := n)
              (.not (selectiveInput state source).output))) ≤
        maximumBits)
    (hnegateWireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveNot (selectiveInput state source).state
                (selectiveInput state source).output))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveNot (selectiveInput state source).state
                (selectiveInput state source).output).output :: spine)) ≤
        maximumBits)
    (hremainingBits : natBitLength remaining ≤ maximumBits)
    (hindexBits : natBitLength (index + 1) ≤ maximumBits)
    (hpc : machine.pc = 18)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = selectiveCountCasesSpineCode spine)
    (hcountdown : machine.registers 18 = remaining)
    (hunaryLeft : machine.registers 19 = 0)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 18 →
      resumed.registers 4 =
        (selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output).state.target -
          (selectiveNot (selectiveInput state source).state
            (selectiveInput state source).output).state.next →
      resumed.registers 6 =
        (selectiveNot (selectiveInput state source).state
          (selectiveInput state source).output).state.next →
      resumed.registers 7 =
        selectiveSelectedCode
          (selectiveNot (selectiveInput state source).state
            (selectiveInput state source).output).state.selected →
      resumed.registers 8 = n →
      resumed.registers 16 = index + 1 →
      resumed.registers 17 =
        selectiveCountCasesSpineCode
          ((selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output).output :: spine) →
      resumed.registers 18 = remaining - 1 →
      resumed.registers 19 = 0 →
      runNPOracleProgram selectiveUnaryProgram maximumBits extraFuel resumed =
        some finalOutput) :
    runNPOracleProgram selectiveUnaryProgram maximumBits
        (5 +
          (5 +
            (emitFuel +
              (7 + (7 + (5 + (negateFuel + (7 + (10 + extraFuel))))))))) machine =
      some finalOutput := by
  have hnodeCode :
      rawCircuitNodeCode (n := n) (.input source) =
        Nat.pair 1 source.val := rfl
  have hnegateCode :
      rawCircuitNodeCode (n := n) (.not (selectiveInput state source).output) =
        Nat.pair 2 (n + (selectiveInput state source).output) := rfl
  have hemitInput :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.input source)) =
        Nat.pair (selectiveStateCode state)
          (rawCircuitNodeCode (n := n) (.input source)) := rfl
  have hnegateEmitInput :
      selectiveEmitInput
          ((selectiveInput state source).state.target -
            (selectiveInput state source).state.next)
          (selectiveInput state source).state.next
          (selectiveSelectedCode (selectiveInput state source).state.selected)
          (rawCircuitNodeCode (n := n)
            (.not (selectiveInput state source).output)) =
        Nat.pair (selectiveStateCode (selectiveInput state source).state)
          (rawCircuitNodeCode (n := n)
            (.not (selectiveInput state source).output)) := rfl
  have hspineForm :
      selectiveCountCasesSpineCode
          ((selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output).output :: spine) =
        Nat.pair 1
          (Nat.pair
            (selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output).output
            (selectiveCountCasesSpineCode spine)) := rfl
  have hcodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.input source)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hinputBits
    rw [hemitInput]
    exact Nat.right_le_pair _ _
  have honeBits : natBitLength 1 ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hcodeBits
    rw [hnodeCode]
    exact Nat.left_le_pair 1 _
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans honeBits
  have hnegateCodeBits :
      natBitLength
          (rawCircuitNodeCode (n := n)
            (.not (selectiveInput state source).output)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hnegateInputBits
    rw [hnegateEmitInput]
    exact Nat.right_le_pair _ _
  have htwoBits : natBitLength 2 ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hnegateCodeBits
    rw [hnegateCode]
    exact Nat.left_le_pair 2 _
  have hchildBits :
      natBitLength (n + (selectiveInput state source).output) ≤ maximumBits := by
    refine (natBitLength_mono ?_).trans hnegateCodeBits
    rw [hnegateCode]
    exact Nat.right_le_pair 2 _
  have hconsBits :
      natBitLength
          (Nat.pair
            (selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output).output
            (selectiveCountCasesSpineCode spine)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  have hremainingLessBits : natBitLength (remaining - 1) ≤ maximumBits :=
    (natBitLength_mono (by omega)).trans hremainingBits
  rw [show 5 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
        (7 + (10 + extraFuel)))))))) =
    (4 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
      (7 + (10 + extraFuel))))))))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUnaryProgram_controllerAt (pc := 18) rfl) hpc]
  rw [if_neg (by rw [hcountdown]; exact hremainingNonzero)]
  rw [show 4 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
        (7 + (10 + extraFuel)))))))) =
    (3 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
      (7 + (10 + extraFuel))))))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 19) rfl) rfl honeBits]
  rw [show 3 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
        (7 + (10 + extraFuel)))))))) =
    (2 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
      (7 + (10 + extraFuel))))))))) + 1 by omega]
  rw [run_pair_instruction (value := rawCircuitNodeCode (n := n) (.input source))
    (selectiveUnaryProgram_controllerAt (pc := 20) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hindex, hnodeCode,
        hsource])
    hcodeBits]
  rw [show 2 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
        (7 + (10 + extraFuel)))))))) =
    (1 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
      (7 + (10 + extraFuel))))))))) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 21) rfl) rfl hzeroBits]
  rw [show 1 + (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
        (7 + (10 + extraFuel)))))))) =
    (5 + (emitFuel + (7 + (7 + (5 + (negateFuel +
      (7 + (10 + extraFuel)))))))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveUnaryProgram_controllerAt (pc := 22) rfl) rfl]
  simp only [ite_self]
  refine run_selectiveUnaryEmitCall state (.input source) hordered maximumBits
    emitFuel (7 + (5 + (negateFuel + (7 + (10 + extraFuel))))) finalOutput n
    index (selectiveCountCasesSpineCode spine) remaining 0
    (machine.registers 27) 0 _ hemitFuel hinputBits hwireBits rfl ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [NPOracleState.write, NPOracleState.jump, hstateRemaining]
  · simp [NPOracleState.write, NPOracleState.jump, hnext]
  · simp [NPOracleState.write, NPOracleState.jump, hselected]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, harity]
  · simp [NPOracleState.write, NPOracleState.jump, hindex]
  · simp [NPOracleState.write, NPOracleState.jump, hspine]
  · simp [NPOracleState.write, NPOracleState.jump, hcountdown]
  · simp [NPOracleState.write, NPOracleState.jump, hunaryLeft]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · intro first hfirstPc _ _ hfirstRemaining hfirstNext hfirstSelected
      hfirstOutput hfirstArity hfirstIndex hfirstSpine hfirstCountdown
      hfirstUnary hfirstAccumulated hfirstPhase
    rw [show 7 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (6 + (5 + (negateFuel + (7 + (10 + extraFuel))))) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 70) rfl) hfirstPc]
    rw [if_pos hfirstPhase]
    rw [show 6 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (5 + (5 + (negateFuel + (7 + (10 + extraFuel))))) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 23) rfl) rfl]
    rw [if_pos (by simp [NPOracleState.jump, hfirstUnary])]
    rw [show 5 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (4 + (5 + (negateFuel + (7 + (10 + extraFuel))))) + 1 by omega]
    rw [run_add_instruction
      (value := n + (selectiveInput state source).output)
      (selectiveUnaryProgram_controllerAt (pc := 29) rfl) rfl
      (by
        simp [NPOracleState.jump, selectiveInput, hfirstArity, hfirstOutput])
      hchildBits]
    rw [show 4 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (3 + (5 + (negateFuel + (7 + (10 + extraFuel))))) + 1 by omega]
    rw [run_set_instruction
      (selectiveUnaryProgram_controllerAt (pc := 30) rfl) rfl htwoBits]
    rw [show 3 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (2 + (5 + (negateFuel + (7 + (10 + extraFuel))))) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        rawCircuitNodeCode (n := n) (.not (selectiveInput state source).output))
      (selectiveUnaryProgram_controllerAt (pc := 31) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hnegateCode])
      hnegateCodeBits]
    rw [show 2 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (1 + (5 + (negateFuel + (7 + (10 + extraFuel))))) + 1 by omega]
    rw [run_set_instruction
      (selectiveUnaryProgram_controllerAt (pc := 32) rfl) rfl honeBits]
    rw [show 1 + (5 + (negateFuel + (7 + (10 + extraFuel)))) =
      (5 + (negateFuel + (7 + (10 + extraFuel)))) + 1 by omega]
    rw [run_branchZero_instruction
      (selectiveUnaryProgram_controllerAt (pc := 33) rfl) rfl]
    simp only [ite_self]
    refine run_selectiveUnaryEmitCall (selectiveInput state source).state
      (.not (selectiveInput state source).output)
      (selectiveState_emit_ordered state (.input source) hordered) maximumBits
      negateFuel (10 + extraFuel) finalOutput n index
      (selectiveCountCasesSpineCode spine) remaining 0 (machine.registers 27) 1
      _ hnegateFuel hnegateInputBits hnegateWireBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveInput] using
        hfirstRemaining
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveInput] using
        hfirstNext
    · simpa [NPOracleState.write, NPOracleState.jump, selectiveInput] using
        hfirstSelected
    · simp [NPOracleState.write, NPOracleState.jump]
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirstArity
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirstIndex
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirstSpine
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirstCountdown
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirstUnary
    · simpa [NPOracleState.write, NPOracleState.jump] using hfirstAccumulated
    · simp [NPOracleState.write, NPOracleState.jump]
    · intro second hsecondPc _ _ hsecondRemaining hsecondNext hsecondSelected
        hsecondOutput hsecondArity hsecondIndex hsecondSpine hsecondCountdown
        hsecondUnary _ hsecondPhase
      rw [show 10 + extraFuel = (9 + extraFuel) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 70) rfl) hsecondPc]
      rw [if_neg (by simp [hsecondPhase])]
      rw [show 9 + extraFuel = (8 + extraFuel) + 1 by omega]
      rw [run_decrement_instruction (value := 0)
        (selectiveUnaryProgram_controllerAt (pc := 71) rfl) rfl
        (by simp [NPOracleState.jump, hsecondPhase]) hzeroBits]
      rw [show 8 + extraFuel = (7 + extraFuel) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 72) rfl) rfl]
      rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
      rw [show 7 + extraFuel = (6 + extraFuel) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          Nat.pair
            (selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output).output
            (selectiveCountCasesSpineCode spine))
        (selectiveUnaryProgram_controllerAt (pc := 34) rfl) rfl
        (by
          simp [NPOracleState.write, NPOracleState.jump, selectiveNot,
            hsecondOutput, hsecondSpine])
        hconsBits]
      rw [show 6 + extraFuel = (5 + extraFuel) + 1 by omega]
      rw [run_set_instruction
        (selectiveUnaryProgram_controllerAt (pc := 35) rfl) rfl honeBits]
      rw [show 5 + extraFuel = (4 + extraFuel) + 1 by omega]
      rw [run_pair_instruction
        (value :=
          selectiveCountCasesSpineCode
            ((selectiveNot (selectiveInput state source).state
                (selectiveInput state source).output).output :: spine))
        (selectiveUnaryProgram_controllerAt (pc := 36) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hspineForm])
        hspineBits]
      rw [show 4 + extraFuel = (3 + extraFuel) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 37) rfl) rfl]
      simp only [ite_self]
      rw [show 3 + extraFuel = (2 + extraFuel) + 1 by omega]
      rw [run_increment_instruction (value := index + 1)
        (selectiveUnaryProgram_controllerAt (pc := 76) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hsecondIndex])
        hindexBits]
      rw [show 2 + extraFuel = (1 + extraFuel) + 1 by omega]
      rw [run_decrement_instruction (value := remaining - 1)
        (selectiveUnaryProgram_controllerAt (pc := 77) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hsecondCountdown])
        hremainingLessBits]
      rw [show 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 78) rfl) rfl]
      simp only [ite_self]
      refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simpa [NPOracleState.write, NPOracleState.jump, selectiveNot] using
          hsecondRemaining
      · simpa [NPOracleState.write, NPOracleState.jump, selectiveNot] using
          hsecondNext
      · simpa [NPOracleState.write, NPOracleState.jump, selectiveNot] using
          hsecondSelected
      · simpa [NPOracleState.write, NPOracleState.jump] using hsecondArity
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simpa [NPOracleState.write, NPOracleState.jump] using hsecondUnary

/-- Compiler wire the controller produces from the conjunct loop head. -/
def selectiveUnaryForwardOutput {n : ℕ} (state : SelectiveState n)
    (literals : List (Fin n × Bool)) (spine : List ℕ) : SelectiveWire n :=
  selectiveUnaryFold
    (selectiveConst
      (selectiveUnaryHeads state
        (literals.map selectiveUnaryConjunct)).state true).state
    (selectiveConst
      (selectiveUnaryHeads state
        (literals.map selectiveUnaryConjunct)).state true).output
    ((selectiveUnaryHeads state
      (literals.map selectiveUnaryConjunct)).values.reverse ++ spine)

private theorem selectiveUnaryForwardOutput_cons {n : ℕ}
    (state : SelectiveState n) (literal : Fin n × Bool)
    (rest : List (Fin n × Bool)) (spine : List ℕ) :
    selectiveUnaryForwardOutput state (literal :: rest) spine =
      selectiveUnaryForwardOutput
        (selectiveCompileExpr state (selectiveUnaryConjunct literal)).state rest
        ((selectiveCompileExpr state
          (selectiveUnaryConjunct literal)).output :: spine) := by
  simp only [selectiveUnaryForwardOutput, List.map_cons, selectiveUnaryHeads,
    List.reverse_cons, List.append_assoc, List.singleton_append]

-- The forward pass is one induction on the conjunct schedule; its exit emits
-- the base `true` and chains straight into the reverse fold.
private theorem run_selectiveUnaryForwardLoop {n : ℕ}
    {index value : ℕ} {literals : List (Fin n × Bool)}
    (hliterals : SelectiveUnaryLiteralsFrom index value literals)
    (state : SelectiveState n) (spine : List ℕ) (maximumBits : ℕ)
    (machine : NPOracleState) (hordered : selectiveStateOrdered state)
    (hbits :
      natBitLength (selectiveUnaryForwardWorkBound state literals spine) ≤
        maximumBits)
    (hvalueBits : natBitLength value ≤ maximumBits)
    (hlengthBits : natBitLength literals.length ≤ maximumBits)
    (hindexBits : natBitLength (index + literals.length) ≤ maximumBits)
    (hpc : machine.pc = 18)
    (hstateRemaining : machine.registers 4 = state.target - state.next)
    (hnext : machine.registers 6 = state.next)
    (hselected : machine.registers 7 = selectiveSelectedCode state.selected)
    (harity : machine.registers 8 = n)
    (hindex : machine.registers 16 = index)
    (hspine : machine.registers 17 = selectiveCountCasesSpineCode spine)
    (hcountdown : machine.registers 18 = literals.length)
    (hunaryLeft : machine.registers 19 = value) :
    runNPOracleProgram selectiveUnaryProgram maximumBits
        (selectiveUnaryForwardFuel state literals spine) machine =
      some
        (selectiveWireCode
          (selectiveUnaryForwardOutput state literals spine)) := by
  induction hliterals generalizing state spine machine with
  | nil index value =>
      have hfuel :
          selectiveUnaryForwardFuel state ([] : List (Fin n × Bool)) spine =
            1 +
              (5 +
                (5 +
                  (selectiveEmitFuel (state.target - state.next)
                      (selectiveSelectedCode state.selected) +
                    (7 +
                      (6 +
                        selectiveUnaryFoldFuel (selectiveConst state true).state
                          (selectiveConst state true).output spine))))) := rfl
      have hboundNil :
          selectiveUnaryForwardWorkBound state ([] : List (Fin n × Bool))
              spine =
            max 2
              (max
                (selectiveEmitInput (state.target - state.next) state.next
                  (selectiveSelectedCode state.selected)
                  (rawCircuitNodeCode (n := n) (.const true)))
                (max
                  (Nat.pair 0 (selectiveWireCode (selectiveConst state true)))
                  (selectiveUnaryFoldWorkBound (selectiveConst state true).state
                    (selectiveConst state true).output spine))) := rfl
      have houtputNil :
          selectiveUnaryForwardOutput state ([] : List (Fin n × Bool)) spine =
            selectiveUnaryFold (selectiveConst state true).state
              (selectiveConst state true).output spine := rfl
      rw [hboundNil] at hbits
      have htwoBits := (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
      have hbitsTail := (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
      have hinputBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTail
      have hbitsTailTwo :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTail
      have hwireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTailTwo
      have hfoldBits :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTailTwo
      have hnodeCode :
          rawCircuitNodeCode (n := n) (.const true) = Nat.pair 0 1 := rfl
      have hemitInput :
          selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := n) (.const true)) =
            Nat.pair (selectiveStateCode state)
              (rawCircuitNodeCode (n := n) (.const true)) := rfl
      have hcodeBits :
          natBitLength (rawCircuitNodeCode (n := n) (.const true)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hinputBits
        rw [hemitInput]
        exact Nat.right_le_pair _ _
      have honeBits : natBitLength 1 ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hcodeBits
        rw [hnodeCode]
        exact Nat.right_le_pair 0 1
      have hzeroBits : natBitLength 0 ≤ maximumBits :=
        (natBitLength_mono (Nat.zero_le _)).trans honeBits
      have houtputWireBits :
          natBitLength (selectiveWireCode (selectiveConst state true)) ≤
            maximumBits :=
        (natBitLength_mono (Nat.right_le_pair 0 _)).trans hwireBits
      have hnextOutputBits :
          natBitLength (selectiveConst state true).output ≤ maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans houtputWireBits
      rw [hfuel, houtputNil]
      rw [show 1 + (5 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine))))) =
        (5 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine))))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 18) rfl) hpc]
      rw [if_pos (by rw [hcountdown]; rfl)]
      rw [show 5 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)))) =
        (4 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveUnaryProgram_controllerAt (pc := 38) rfl) rfl hzeroBits]
      rw [show 4 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)))) =
        (3 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveUnaryProgram_controllerAt (pc := 39) rfl) rfl honeBits]
      rw [show 3 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)))) =
        (2 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine))))) + 1 by omega]
      rw [run_pair_instruction
        (value := rawCircuitNodeCode (n := n) (.const true))
        (selectiveUnaryProgram_controllerAt (pc := 40) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode])
        hcodeBits]
      rw [show 2 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)))) =
        (1 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine))))) + 1 by omega]
      rw [run_set_instruction
        (selectiveUnaryProgram_controllerAt (pc := 41) rfl) rfl htwoBits]
      rw [show 1 + (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)))) =
        (5 + (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (7 + (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)))) + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveUnaryProgram_controllerAt (pc := 42) rfl) rfl]
      simp only [ite_self]
      refine run_selectiveUnaryEmitCall state (.const true) hordered maximumBits
        _ (6 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine)
        _ n index (selectiveCountCasesSpineCode spine) 0 value
        (machine.registers 27) 2 _ rfl hinputBits hwireBits rfl ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hstateRemaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hindex]
      · simp [NPOracleState.write, NPOracleState.jump, hspine]
      · simp [NPOracleState.write, NPOracleState.jump, hcountdown]
      · simp [NPOracleState.write, NPOracleState.jump, hunaryLeft]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedWire _ hresumedRemaining hresumedNext
          hresumedSelected hresumedOutput hresumedArity _ hresumedSpine _ _ _
          hresumedPhase
        rw [show 6 + selectiveUnaryFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine =
          (5 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveUnaryProgram_controllerAt (pc := 70) rfl) hresumedPc]
        rw [if_neg (by simp [hresumedPhase])]
        rw [show 5 + selectiveUnaryFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine =
          (4 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine) + 1 by omega]
        rw [run_decrement_instruction (value := 1)
          (selectiveUnaryProgram_controllerAt (pc := 71) rfl) rfl
          (by simp [NPOracleState.jump, hresumedPhase]) honeBits]
        rw [show 4 + selectiveUnaryFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine =
          (3 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveUnaryProgram_controllerAt (pc := 72) rfl) rfl]
        rw [if_neg (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [show 3 + selectiveUnaryFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine =
          (2 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine) + 1 by omega]
        rw [run_decrement_instruction (value := 0)
          (selectiveUnaryProgram_controllerAt (pc := 73) rfl) rfl
          (by simp [NPOracleState.write, NPOracleState.jump]) hzeroBits]
        rw [show 2 + selectiveUnaryFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine =
          (1 + selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine) + 1 by omega]
        rw [run_branchZero_instruction
          (selectiveUnaryProgram_controllerAt (pc := 74) rfl) rfl]
        rw [if_pos (by simp [NPOracleState.write, NPOracleState.jump])]
        rw [show 1 + selectiveUnaryFoldFuel (selectiveConst state true).state
              (selectiveConst state true).output spine =
          selectiveUnaryFoldFuel (selectiveConst state true).state
            (selectiveConst state true).output spine + 1 by omega]
        rw [run_copy_instruction (value := (selectiveConst state true).output)
          (selectiveUnaryProgram_controllerAt (pc := 43) rfl) rfl
          (by
            simp [NPOracleState.write, NPOracleState.jump, selectiveConst,
              hresumedOutput])
          hnextOutputBits]
        refine run_selectiveUnaryFoldLoop spine (selectiveConst state true).state
          (selectiveConst state true).output
          (selectiveState_emit_ordered state (.const true) hordered) maximumBits
          hfoldBits _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  | positive hsource hvalue hrest ih =>
      rename_i index value source rest
      have hfuel :
          selectiveUnaryForwardFuel state ((source, true) :: rest) spine =
            5 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    (10 +
                      selectiveUnaryForwardFuel
                        (selectiveInput state source).state rest
                        ((selectiveInput state source).output ::
                          spine))))) := by
        simp only [selectiveUnaryForwardFuel, if_pos]
      have hboundCons :
          selectiveUnaryForwardWorkBound state ((source, true) :: rest) spine =
            max
              (selectiveEmitInput (state.target - state.next) state.next
                (selectiveSelectedCode state.selected)
                (rawCircuitNodeCode (n := n) (.input source)))
              (max
                (Nat.pair 0 (selectiveWireCode (selectiveInput state source)))
                (max
                  (selectiveCountCasesSpineCode
                    ((selectiveInput state source).output :: spine))
                  (selectiveUnaryForwardWorkBound
                    (selectiveInput state source).state rest
                    ((selectiveInput state source).output :: spine)))) := by
        simp only [selectiveUnaryForwardWorkBound, if_pos]
      have hconjunct :
          selectiveCompileExpr state
              (selectiveUnaryConjunct ((source, true) : Fin n × Bool)) =
            selectiveInput state source := rfl
      rw [hboundCons] at hbits
      have hinputBits := (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
      have hbitsOne := (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
      have hwireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsOne
      have hbitsTwo :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsOne
      have hspineBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTwo
      have hrecBits :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTwo
      simp only [List.length_cons] at hlengthBits hindexBits hcountdown
      rw [hfuel, selectiveUnaryForwardOutput_cons, hconjunct]
      refine run_selectiveUnaryPositiveStep state source index value
        (rest.length + 1) spine hordered maximumBits _ _ _ machine rfl hsource
        hvalue (by omega) hinputBits hwireBits hspineBits hvalueBits
        hlengthBits (by
          refine (natBitLength_mono ?_).trans hindexBits
          omega) hpc hstateRemaining hnext hselected harity hindex hspine
        hcountdown hunaryLeft ?_
      intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedArity hresumedIndex hresumedSpine hresumedCountdown
        hresumedUnary
      refine ih (selectiveInput state source).state _ resumed
        (selectiveState_emit_ordered state (.input source) hordered) hrecBits
        ((natBitLength_mono (by omega)).trans hvalueBits)
        ((natBitLength_mono (by omega)).trans hlengthBits)
        ((natBitLength_mono (by omega)).trans hindexBits) hresumedPc
        hresumedRemaining hresumedNext hresumedSelected hresumedArity
        hresumedIndex hresumedSpine ?_ hresumedUnary
      · simpa using hresumedCountdown
  | negative hsource hrest ih =>
      rename_i index source rest
      have hfuel :
          selectiveUnaryForwardFuel state ((source, false) :: rest) spine =
            5 +
              (5 +
                (selectiveEmitFuel (state.target - state.next)
                    (selectiveSelectedCode state.selected) +
                  (7 +
                    (7 +
                      (5 +
                        (selectiveEmitFuel
                            ((selectiveInput state source).state.target -
                              (selectiveInput state source).state.next)
                            (selectiveSelectedCode
                              (selectiveInput state source).state.selected) +
                          (7 +
                            (10 +
                              selectiveUnaryForwardFuel
                                (selectiveNot (selectiveInput state source).state
                                  (selectiveInput state source).output).state
                                rest
                                ((selectiveNot
                                    (selectiveInput state source).state
                                    (selectiveInput state source).output).output ::
                                  spine))))))))) := rfl
      have hboundCons :
          selectiveUnaryForwardWorkBound state ((source, false) :: rest) spine =
            max
              (selectiveEmitInput (state.target - state.next) state.next
                (selectiveSelectedCode state.selected)
                (rawCircuitNodeCode (n := n) (.input source)))
              (max
                (Nat.pair 0 (selectiveWireCode (selectiveInput state source)))
                (max
                  (selectiveEmitInput
                    ((selectiveInput state source).state.target -
                      (selectiveInput state source).state.next)
                    (selectiveInput state source).state.next
                    (selectiveSelectedCode
                      (selectiveInput state source).state.selected)
                    (rawCircuitNodeCode (n := n)
                      (.not (selectiveInput state source).output)))
                  (max
                    (Nat.pair 0
                      (selectiveWireCode
                        (selectiveNot (selectiveInput state source).state
                          (selectiveInput state source).output)))
                    (max
                      (selectiveCountCasesSpineCode
                        ((selectiveNot (selectiveInput state source).state
                            (selectiveInput state source).output).output ::
                          spine))
                      (selectiveUnaryForwardWorkBound
                        (selectiveNot (selectiveInput state source).state
                          (selectiveInput state source).output).state rest
                        ((selectiveNot (selectiveInput state source).state
                            (selectiveInput state source).output).output ::
                          spine)))))) := rfl
      have hconjunct :
          selectiveCompileExpr state
              (selectiveUnaryConjunct ((source, false) : Fin n × Bool)) =
            selectiveNot (selectiveInput state source).state
              (selectiveInput state source).output := rfl
      rw [hboundCons] at hbits
      have hinputBits := (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
      have hbitsOne := (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
      have hwireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsOne
      have hbitsTwo :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsOne
      have hnegateInputBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTwo
      have hbitsThree :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTwo
      have hnegateWireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsThree
      have hbitsFour :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsThree
      have hspineBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsFour
      have hrecBits :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsFour
      simp only [List.length_cons] at hlengthBits hindexBits hcountdown
      rw [hfuel, selectiveUnaryForwardOutput_cons, hconjunct]
      refine run_selectiveUnaryNegativeStep state source index
        (rest.length + 1) spine hordered maximumBits _ _ _ _ machine rfl rfl
        hsource (by omega) hinputBits hwireBits hnegateInputBits
        hnegateWireBits hspineBits hlengthBits (by
          refine (natBitLength_mono ?_).trans hindexBits
          omega) hpc hstateRemaining hnext hselected harity hindex hspine
        hcountdown hunaryLeft ?_
      intro resumed hresumedPc hresumedRemaining hresumedNext hresumedSelected
        hresumedArity hresumedIndex hresumedSpine hresumedCountdown
        hresumedUnary
      refine ih _ _ resumed
        (selectiveState_emit_ordered _ _
          (selectiveState_emit_ordered state (.input source) hordered))
        hrecBits hvalueBits
        ((natBitLength_mono (by omega)).trans hlengthBits)
        ((natBitLength_mono (by omega)).trans hindexBits) hresumedPc
        hresumedRemaining hresumedNext hresumedSelected hresumedArity
        hresumedIndex hresumedSpine ?_ hresumedUnary
      · simpa using hresumedCountdown

/-! ## 6. The whole 97-instruction stream -/

/-- Register width of one whole unary-equality compilation. -/
def selectiveUnaryRunBits {n : ℕ} (state : SelectiveState n)
    (literals : List (Fin n × Bool)) (rowBase start value : ℕ) : ℕ :=
  max
    (natBitLength
      (selectiveUnaryInput (selectiveStateCode state) n rowBase start
        literals.length value)) <|
    max (natBitLength (rowBase + start + literals.length))
      (natBitLength (selectiveUnaryForwardWorkBound state literals []))

/-- Interpreter fuel of one whole unary-equality compilation. -/
def selectiveUnaryRunFuel {n : ℕ} (state : SelectiveState n)
    (literals : List (Fin n × Bool)) : ℕ :=
  18 + selectiveUnaryForwardFuel state literals []

private theorem selectiveUnaryForwardOutput_nil_eq {n : ℕ}
    (state : SelectiveState n) (literals : List (Fin n × Bool)) :
    selectiveUnaryForwardOutput state literals [] =
      selectiveCompileExpr state
        (BoolExpr.all (literals.map selectiveUnaryConjunct)) := by
  rw [selectiveCompileExpr_all_eq_fold]
  simp only [selectiveUnaryForwardOutput, List.append_nil]

-- The eighteen-step request parser feeds the conjunct loop head.
/-- **The unary-equality compiler's run.**  The `97`-instruction stream started
on its own ABI frame, at any entry registers, returns exactly the compiler wire
the source compiler produces for the conjunction of the scheduled literals.
Nothing on this level is left as a premise. -/
theorem run_selectiveUnaryProgram {n : ℕ} (state : SelectiveState n)
    (literals : List (Fin n × Bool)) (rowBase start value : ℕ)
    (hliterals : SelectiveUnaryLiteralsFrom (rowBase + start) value literals)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveUnaryInput (selectiveStateCode state) n rowBase start
          literals.length value) :
    runNPOracleProgram selectiveUnaryProgram
        (selectiveUnaryRunBits state literals rowBase start value)
        (selectiveUnaryRunFuel state literals) entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (BoolExpr.all (literals.map selectiveUnaryConjunct)))) := by
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hrequestBits :
      natBitLength
          (selectiveUnaryInput (selectiveStateCode state) n rowBase start
            literals.length value) ≤
        selectiveUnaryRunBits state literals rowBase start value :=
    Nat.le_max_left _ _
  have htail :
      max (natBitLength (rowBase + start + literals.length))
          (natBitLength (selectiveUnaryForwardWorkBound state literals [])) ≤
        selectiveUnaryRunBits state literals rowBase start value :=
    Nat.le_max_right _ _
  have hsumBits := (Nat.le_max_left _ _).trans htail
  have hforwardBits := (Nat.le_max_right _ _).trans htail
  have hflat := hrequestBits
  simp only [selectiveUnaryInput] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have harityBits := natBitLength_pair_left hone
  have htwo := natBitLength_pair_right hone
  have hrowBaseBits := natBitLength_pair_left htwo
  have hthree := natBitLength_pair_right htwo
  have hstartBits := natBitLength_pair_left hthree
  have hfour := natBitLength_pair_right hthree
  have hlimitBits := natBitLength_pair_left hfour
  have hvalueBits := natBitLength_pair_right hfour
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have hnextSelectedBits := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left hnextSelectedBits
  have hselectedBits := natBitLength_pair_right hnextSelectedBits
  have hzeroBits :
      natBitLength 0 ≤ selectiveUnaryRunBits state literals rowBase start value :=
    (natBitLength_mono (Nat.zero_le _)).trans hlimitBits
  have hindexBits :
      natBitLength (rowBase + start) ≤
        selectiveUnaryRunBits state literals rowBase start value :=
    (natBitLength_mono (by omega)).trans hsumBits
  rw [selectiveUnaryRunFuel]
  rw [show 18 + selectiveUnaryForwardFuel state literals [] =
    (17 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveUnaryProgram_controllerAt (pc := 0) rfl) hentryPc
    (by simp [hentryInput, selectiveUnaryInput]) hstateBits]
  rw [show 17 + selectiveUnaryForwardFuel state literals [] =
    (16 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair n <|
        Nat.pair rowBase <|
          Nat.pair start (Nat.pair literals.length value))
    (selectiveUnaryProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        selectiveUnaryInput])
    hone]
  rw [show 16 + selectiveUnaryForwardFuel state literals [] =
    (15 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveUnaryProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [show 15 + selectiveUnaryForwardFuel state literals [] =
    (14 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveUnaryProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hnextSelectedBits]
  rw [show 14 + selectiveUnaryForwardFuel state literals [] =
    (13 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveUnaryProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [show 13 + selectiveUnaryForwardFuel state literals [] =
    (12 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveUnaryProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [show 12 + selectiveUnaryForwardFuel state literals [] =
    (11 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := n)
    (selectiveUnaryProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 11 + selectiveUnaryForwardFuel state literals [] =
    (10 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair rowBase (Nat.pair start (Nat.pair literals.length value)))
    (selectiveUnaryProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [show 10 + selectiveUnaryForwardFuel state literals [] =
    (9 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := rowBase)
    (selectiveUnaryProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowBaseBits]
  rw [show 9 + selectiveUnaryForwardFuel state literals [] =
    (8 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair start (Nat.pair literals.length value))
    (selectiveUnaryProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 8 + selectiveUnaryForwardFuel state literals [] =
    (7 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := start)
    (selectiveUnaryProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hstartBits]
  rw [show 7 + selectiveUnaryForwardFuel state literals [] =
    (6 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair literals.length value)
    (selectiveUnaryProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [show 6 + selectiveUnaryForwardFuel state literals [] =
    (5 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairLeft_instruction (value := literals.length)
    (selectiveUnaryProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlimitBits]
  rw [show 5 + selectiveUnaryForwardFuel state literals [] =
    (4 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_unpairRight_instruction (value := value)
    (selectiveUnaryProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 4 + selectiveUnaryForwardFuel state literals [] =
    (3 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_add_instruction (value := rowBase + start)
    (selectiveUnaryProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hindexBits]
  rw [show 3 + selectiveUnaryForwardFuel state literals [] =
    (2 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_set_instruction
    (selectiveUnaryProgram_controllerAt (pc := 15) rfl) rfl hzeroBits]
  rw [show 2 + selectiveUnaryForwardFuel state literals [] =
    (1 + selectiveUnaryForwardFuel state literals []) + 1 by omega]
  rw [run_copy_instruction (value := literals.length)
    (selectiveUnaryProgram_controllerAt (pc := 16) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hlimitBits]
  rw [show 1 + selectiveUnaryForwardFuel state literals [] =
    selectiveUnaryForwardFuel state literals [] + 1 by omega]
  rw [run_copy_instruction (value := value)
    (selectiveUnaryProgram_controllerAt (pc := 17) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [← selectiveUnaryForwardOutput_nil_eq]
  refine run_selectiveUnaryForwardLoop hliterals state [] _ _ hordered
    hforwardBits hvalueBits hlimitBits hsumBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [NPOracleState.write, NPOracleState.jump,
      selectiveCountCasesSpineCode]

/-! ## 7. The level premise, discharged

`unaryEqualsExpr` is the only expression this controller is ever asked to
compile: the field, address, tag and grammar selectors all reach it through one
of the three unary blocks of a description row.  §7 exhibits its conjunct
schedule and discharges the whole level. -/

/-- The conjunct schedule of one unary equality test. -/
def selectiveUnaryEqualsLiterals {n bound : ℕ} (row : Fin (bound + 1)) :
    (start limit value : ℕ) → start + limit ≤ rowWidth n bound →
      List (Fin (descriptionWidth n bound) × Bool)
  | _, 0, _, _ => []
  | start, limit + 1, value, hblock =>
      (descriptionIndex row ⟨start, by omega⟩, decide (0 < value)) ::
        selectiveUnaryEqualsLiterals row (start + 1) limit (value - 1)
          (by omega)

@[simp] theorem selectiveUnaryEqualsLiterals_length {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    (selectiveUnaryEqualsLiterals (n := n) row start limit value
      hblock).length = limit := by
  induction limit generalizing start value with
  | zero => rfl
  | succ limit ih =>
      simp only [selectiveUnaryEqualsLiterals, List.length_cons]
      rw [ih]

theorem selectiveUnaryEqualsLiterals_from {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    SelectiveUnaryLiteralsFrom (row.val * rowWidth n bound + start) value
      (selectiveUnaryEqualsLiterals (n := n) row start limit value hblock) := by
  induction limit generalizing start value with
  | zero => exact SelectiveUnaryLiteralsFrom.nil _ _
  | succ limit ih =>
      rw [selectiveUnaryEqualsLiterals]
      rcases Nat.eq_zero_or_pos value with hvalue | hvalue
      · subst hvalue
        rw [show decide (0 < 0) = false by simp]
        refine SelectiveUnaryLiteralsFrom.negative ?_ ?_
        · simp [descriptionIndex]
        · have hrest := ih (start + 1) 0 (by omega)
          rw [show row.val * rowWidth n bound + (start + 1) =
            row.val * rowWidth n bound + start + 1 by omega] at hrest
          exact hrest
      · rw [show decide (0 < value) = true by simp [hvalue]]
        refine SelectiveUnaryLiteralsFrom.positive ?_ (by omega) ?_
        · simp [descriptionIndex]
        · have hrest := ih (start + 1) (value - 1) (by omega)
          rw [show row.val * rowWidth n bound + (start + 1) =
            row.val * rowWidth n bound + start + 1 by omega] at hrest
          exact hrest

theorem boolExpr_all_selectiveUnaryEqualsLiterals {n bound : ℕ}
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound) :
    BoolExpr.all
        ((selectiveUnaryEqualsLiterals (n := n) row start limit value
          hblock).map selectiveUnaryConjunct) =
      unaryEqualsExpr (n := n) row start limit value hblock := by
  induction limit generalizing start value with
  | zero => rfl
  | succ limit ih =>
      have htail := ih (start + 1) (value - 1) (by omega)
      rw [selectiveUnaryEqualsLiterals, List.map_cons, BoolExpr.all, htail]
      simp only [unaryEqualsExpr, List.ofFn_succ, BoolExpr.all]
      refine congrArg₂ BoolExpr.and ?_ (congrArg BoolExpr.all ?_)
      · by_cases hzero : 0 < value <;>
          simp [selectiveUnaryConjunct, hzero]
      · refine congrArg List.ofFn (funext fun offset => ?_)
        have hlt : (offset.val < value - 1) ↔ (offset.succ.val < value) := by
          simp only [Fin.val_succ]
          omega
        have hindex :
            descriptionIndex (n := n) row
                ⟨start + 1 + offset.val, by omega⟩ =
              descriptionIndex (n := n) row
                ⟨start + offset.succ.val, by omega⟩ := by
          apply Fin.ext
          simp only [descriptionIndex, Fin.val_succ]
          omega
        by_cases hcase : offset.val < value - 1
        · rw [if_pos hcase, if_pos (hlt.mp hcase), hindex]
        · rw [if_neg hcase, if_neg (fun hother => hcase (hlt.mpr hother)),
            hindex]

/-- **Level premise, discharged.**  The unary compiler's run at its own ABI
frame, at an arbitrary entry state.  This is the shape every caller of
`selectiveUnaryProgram` consumes; unlike the levels above it, it is a theorem
rather than a structure field. -/
theorem run_selectiveUnaryProgram_eq_unaryEquals {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (start limit value : ℕ)
    (hblock : start + limit ≤ rowWidth n bound)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveUnaryInput (selectiveStateCode state)
          (descriptionWidth n bound) (row.val * rowWidth n bound) start limit
          value) :
    runNPOracleProgram selectiveUnaryProgram
        (selectiveUnaryRunBits state
          (selectiveUnaryEqualsLiterals (n := n) row start limit value hblock)
          (row.val * rowWidth n bound) start value)
        (selectiveUnaryRunFuel state
          (selectiveUnaryEqualsLiterals (n := n) row start limit value hblock))
        entry =
      some
        (selectiveWireCode
          (selectiveCompileExpr state
            (unaryEqualsExpr (n := n) row start limit value hblock))) := by
  rw [← boolExpr_all_selectiveUnaryEqualsLiterals row start limit value hblock]
  refine run_selectiveUnaryProgram state _ (row.val * rowWidth n bound) start
    value (selectiveUnaryEqualsLiterals_from row start limit value hblock)
    hordered entry hentryPc ?_
  rw [hentryInput, selectiveUnaryEqualsLiterals_length]

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
