import Proof.MachineModel.BoundedOracleStructuralSelectiveProgram
import Proof.MachineModel.TotalSelectiveFixedCountProgram

/-!
# The nested structural compiler's outermost run

`totalSelectiveCountCasesProgram` is the 3052-instruction stream whose execution is
the sole remaining premise of the emitter chain.  It is a controller of `61`
instructions with two relocated callees: the `2973`-instruction fixed-count
sub-compiler and the `18`-instruction append transition.

This module executes the controller.  Its forward pass compiles one candidate
node count per iteration through the fixed-count callee and retains every
candidate output on a private reverse spine; its reverse pass then rebuilds the
source compiler's right-associated disjunction with its explicit `false` base
case, one append per spine entry.  Both passes are proved here.  The
fixed-count callee's own run is the single named level premise
(`SelectiveFixedCountProgramRunner`); everything else on this level,
including the
typed reachability invariant the append transition needs, is discharged.
-/

namespace NearCubicWires.TotalSelectiveCountCasesProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CircuitInputClauseProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

open NearCubicWires.TotalSelectiveFixedCountProgram

set_option maxRecDepth 100000 in
@[simp] private theorem totalSelectiveFixedCountProgram_length :
    totalSelectiveFixedCountProgram.length = 2973 := by
  rfl

def totalSelectiveCountCasesProgram : NPOracleProgram :=
  selectiveCountCasesControllerProgram 61 3034 ++
    totalSelectiveFixedCountProgram.map
      (callableInstruction 61 1000 50 29) ++
    selectiveEmitProgram.map
      (callableInstruction 3034 67000 50 57)

/-! ## 1. The typed append invariant through the whole compiler

`selectiveStateOrdered` is the reachability invariant the machine append
transition needs at every call site.  Every typed compiler stage is a
composition of appends, so the invariant propagates by structural induction.
-/

theorem selectiveCompileExpr_ordered {n : ℕ}
    (state : SelectiveState n) (expr : BoolExpr n)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered (selectiveCompileExpr state expr).state := by
  induction expr generalizing state with
  | const value =>
      exact selectiveState_emit_ordered state (.const value) hordered
  | input index =>
      exact selectiveState_emit_ordered state (.input index) hordered
  | not child ih =>
      exact selectiveState_emit_ordered _ _ (ih state hordered)
  | and left right ihLeft ihRight =>
      exact selectiveState_emit_ordered _ _
        (ihRight _ (ihLeft state hordered))
  | or left right ihLeft ihRight =>
      exact selectiveState_emit_ordered _ _
        (ihRight _ (ihLeft state hordered))

private theorem selectiveCompileGuardedAny_ordered {n : ℕ}
    (choices : List (BoolExpr n × ℕ)) (state : SelectiveState n)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileGuardedAny state choices).state := by
  induction choices generalizing state with
  | nil =>
      rw [selectiveCompileGuardedAny]
      exact selectiveState_emit_ordered state (.const false) hordered
  | cons choice rest ih =>
      rw [selectiveCompileGuardedAny]
      refine selectiveState_emit_ordered _ _ (ih _ ?_)
      exact selectiveState_emit_ordered _ _
        (selectiveCompileExpr_ordered state choice.1 hordered)

private theorem selectiveCompileFieldSelect_ordered {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (fieldEquals : Fin (bound + 1) → ℕ →
      BoolExpr (descriptionWidth n bound))
    (row : Fin (bound + 1)) (values : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileFieldSelect state fieldEquals row values).state :=
  selectiveCompileGuardedAny_ordered _ state hordered

private theorem selectiveCompileUniversalNode_ordered {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (row : Fin (bound + 1)) (address : BitInput n) (priorValues : List ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileUniversalNode state row address priorValues).state := by
  refine selectiveCompileGuardedAny_ordered _ _ ?_
  refine selectiveState_emit_ordered _ _ ?_
  refine selectiveState_emit_ordered _ _ ?_
  refine selectiveState_emit_ordered _ _ ?_
  refine selectiveCompileExpr_ordered _ _ ?_
  refine selectiveCompileExpr_ordered _ _ ?_
  exact selectiveCompileFieldSelect_ordered _ _ _ _
    (selectiveCompileFieldSelect_ordered _ _ _ _ hordered)

private theorem selectiveCompileUniversalNodes_ordered {n bound : ℕ}
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (state : SelectiveState (descriptionWidth n bound))
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileUniversalNodes state address count hcount).state := by
  induction count with
  | zero => exact hordered
  | succ count ih =>
      exact selectiveCompileUniversalNode_ordered _ _ _ _
        (ih (by omega))

private theorem selectiveCompileUniversalOutput_ordered {n bound : ℕ}
    (state : SelectiveState (descriptionWidth n bound))
    (address : BitInput n) (count : ℕ) (hcount : count ≤ bound)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileUniversalOutput state address count hcount).state :=
  selectiveCompileFieldSelect_ordered _ _ _ _
    (selectiveCompileUniversalNodes_ordered address count hcount state hordered)

private theorem selectiveCompileUniversalOutputs_ordered {n bound : ℕ}
    (count : ℕ) (hcount : count ≤ bound) (addresses : List (BitInput n))
    (state : SelectiveState (descriptionWidth n bound))
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileUniversalOutputs state count hcount addresses).state := by
  induction addresses generalizing state with
  | nil => exact hordered
  | cons address rest ih =>
      exact ih _
        (selectiveCompileUniversalOutput_ordered state address count hcount
          hordered)

private theorem selectiveCompileLiteral_ordered {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ) (literal : Literal q)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileLiteral state values literal).state := by
  cases literal with
  | positive query => exact hordered
  | negative query =>
      exact selectiveState_emit_ordered _ _ hordered

private theorem selectiveCompileClause_ordered {q n : ℕ}
    (state : SelectiveState n) (values : List ℕ)
    (clause : Fin 3 → Literal q)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileClause state values clause).state := by
  refine selectiveState_emit_ordered _ _ ?_
  refine selectiveCompileLiteral_ordered _ _ _ ?_
  refine selectiveState_emit_ordered _ _ ?_
  refine selectiveCompileLiteral_ordered _ _ _ ?_
  exact selectiveCompileLiteral_ordered _ _ _ hordered

private theorem selectiveCompileClauses_ordered {q n : ℕ}
    (clauses : List (Fin 3 → Literal q)) (state : SelectiveState n)
    (values : List ℕ) (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileClauses state values clauses).state := by
  induction clauses generalizing state with
  | nil => exact selectiveState_emit_ordered state (.const true) hordered
  | cons clause rest ih =>
      exact selectiveState_emit_ordered _ _
        (ih _ (selectiveCompileClause_ordered state values clause hordered))

private theorem selectiveCompileTableVerifierRow_ordered
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (randomnessCode : ℕ)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileTableVerifierRow outputs width count bound state
        nodeCount hnodeCount randomnessCode).state :=
  selectiveCompileClauses_ordered _ _ _
    (selectiveCompileUniversalOutputs_ordered nodeCount hnodeCount _ state
      hordered)

theorem selectiveCompileTableVerifierRows_ordered
    (outputs : List ℕ) (width count bound : ℕ)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (randomnessCodes : List ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileTableVerifierRows outputs width count bound nodeCount
        hnodeCount state randomnessCodes).state := by
  induction randomnessCodes generalizing state with
  | nil => exact selectiveState_emit_ordered state (.const true) hordered
  | cons randomnessCode rest ih =>
      exact selectiveState_emit_ordered _ _
        (ih _
          (selectiveCompileTableVerifierRow_ordered outputs width count bound
            state nodeCount hnodeCount randomnessCode hordered))

/-- **The typed append invariant at the fixed-count level.**  Compiling one
candidate node count from a reachable state leaves a reachable state. -/
theorem selectiveCompileTableFixedCount_ordered
    (outputs : List ℕ) (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound)
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCompileTableFixedCount outputs width count bound state
        candidate).state :=
  selectiveState_emit_ordered _ _
    (selectiveCompileTableVerifierRows_ordered outputs width count bound
      (candidate.val + 1) (by omega) _ _
      (selectiveCompileExpr_ordered state _ hordered))

/-! ## 2. The controller's two passes, at the typed level

The source compiler folds one candidate at a time and emits the disjunction of
each candidate against the compiled tail.  The controller instead runs every
candidate first, retains their outputs on a reverse spine, and only then emits
the disjunctions from the innermost outwards.  Both orders append exactly the
same nodes in exactly the same order; §2 proves that.
-/

/-- The controller's private reverse spine: empty, or one tagged cons cell. -/
def selectiveCountCasesSpineCode : List ℕ → ℕ
  | [] => 0
  | value :: rest =>
      Nat.pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))

/-- The forward pass: one compiled candidate output per candidate, in the
ascending order the controller visits them. -/
def selectiveCountCasesHeads (outputs : List ℕ) (width count bound : ℕ) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      SelectiveWireList (descriptionWidth width bound)
  | state, [] => { state := state, values := [] }
  | state, candidate :: rest =>
      let head :=
        selectiveCompileTableFixedCount outputs width count bound state
          candidate
      let tail :=
        selectiveCountCasesHeads outputs width count bound head.state rest
      { state := tail.state
        values := head.output :: tail.values }

/-- The reverse pass: one disjunction per retained candidate output. -/
def selectiveCountCasesFold {n : ℕ} :
    SelectiveState n → ℕ → List ℕ → SelectiveWire n
  | state, accumulated, [] => { state := state, output := accumulated }
  | state, accumulated, value :: rest =>
      let combined := selectiveOr state value accumulated
      selectiveCountCasesFold combined.state combined.output rest

theorem selectiveCountCasesFold_concat {n : ℕ} (values : List ℕ)
    (state : SelectiveState n) (accumulated value : ℕ) :
    selectiveCountCasesFold state accumulated (values ++ [value]) =
      selectiveOr (selectiveCountCasesFold state accumulated values).state
        value (selectiveCountCasesFold state accumulated values).output := by
  induction values generalizing state accumulated with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.cons_append, selectiveCountCasesFold]
      exact ih _ _

theorem selectiveCountCasesHeads_ordered (outputs : List ℕ)
    (width count bound : ℕ) (candidates : List (Fin bound))
    (state : SelectiveState (descriptionWidth width bound))
    (hordered : selectiveStateOrdered state) :
    selectiveStateOrdered
      (selectiveCountCasesHeads outputs width count bound state
        candidates).state := by
  induction candidates generalizing state with
  | nil => exact hordered
  | cons candidate rest ih =>
      exact ih _
        (selectiveCompileTableFixedCount_ordered outputs width count bound
          state candidate hordered)

/-- **The controller's scheduling identity.**  The source compiler's
right-associated disjunction is exactly the forward candidate pass followed by
the reverse fold over the retained spine. -/
theorem selectiveCompileTableCountCases_eq_fold (outputs : List ℕ)
    (width count bound : ℕ) (candidates : List (Fin bound))
    (state : SelectiveState (descriptionWidth width bound)) :
    selectiveCompileTableCountCases outputs width count bound state
        candidates =
      selectiveCountCasesFold
        (selectiveConst
          (selectiveCountCasesHeads outputs width count bound state
            candidates).state false).state
        (selectiveConst
          (selectiveCountCasesHeads outputs width count bound state
            candidates).state false).output
        (selectiveCountCasesHeads outputs width count bound state
          candidates).values.reverse := by
  induction candidates generalizing state with
  | nil => rfl
  | cons candidate rest ih =>
      simp only [selectiveCompileTableCountCases, selectiveCountCasesHeads,
        List.reverse_cons]
      rw [selectiveCountCasesFold_concat]
      rw [ih]

/-! ## 3. Decoding the fixed 3052-instruction stream

The controller occupies the first `61` positions, the fixed-count callee the
next `2973`, and the append callee the last `18`.  Every later step decodes
through exactly one of the three lemmas below, so no proof ever forces the
whole instruction list.
-/

private theorem totalSelectiveCountCasesProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveCountCasesControllerProgram 61 3034)[pc]? = some instruction) :
    totalSelectiveCountCasesProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveCountCasesControllerProgram 61 3034).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveCountCasesControllerProgram_length] at hpc
  simp only [totalSelectiveCountCasesProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveCountCasesControllerProgram_length,
      totalSelectiveFixedCountProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveCountCasesControllerProgram_length]
    omega)]
  exact hlookup

theorem totalSelectiveCountCasesProgram_fixedCountCallable :
    ProgramCallableAt totalSelectiveCountCasesProgram totalSelectiveFixedCountProgram
      61 1000 50 29 := by
  intro pc instruction hlookup
  have hpc : pc < totalSelectiveFixedCountProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [totalSelectiveFixedCountProgram_length] at hpc
  simp only [totalSelectiveCountCasesProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveCountCasesControllerProgram_length,
      totalSelectiveFixedCountProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveCountCasesControllerProgram_length]
    omega)]
  simp only [selectiveCountCasesControllerProgram_length]
  rw [show 61 + pc - 61 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

theorem totalSelectiveCountCasesProgram_emitCallable :
    ProgramCallableAt totalSelectiveCountCasesProgram selectiveEmitProgram
      3034 67000 50 57 := by
  intro pc instruction hlookup
  simp only [totalSelectiveCountCasesProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveCountCasesControllerProgram_length,
      totalSelectiveFixedCountProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveCountCasesControllerProgram_length,
    totalSelectiveFixedCountProgram_length]
  rw [show 3034 + pc - (61 + 2973) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 4. One relocated call

Every call site writes the callee's request register, zeroes the shared
accumulator, and jumps to the callee base.  The callee's own run is consumed at
whatever entry registers the previous call left behind, so each level's runner
is required to hold at an arbitrary entry state. -/

private theorem relocateActiveState_self (pcOffset registerOffset span : ℕ)
    (machine : NPOracleState) (hpc : machine.pc = pcOffset) :
    machine =
      relocateActiveState pcOffset registerOffset span machine.registers
        { pc := 0
          registers := fun register => machine.registers (registerOffset + register) } := by
  refine state_ext _ _ ?_ ?_
  · simp [relocateActiveState, hpc]
  · funext candidate
    by_cases hlower : registerOffset ≤ candidate
    · by_cases hupper : candidate < registerOffset + span
      · rw [show
          (relocateActiveState pcOffset registerOffset span machine.registers
            { pc := 0
              registers := fun register =>
                machine.registers (registerOffset + register) }).registers
              candidate =
            machine.registers (registerOffset + (candidate - registerOffset)) by
          simp [relocateActiveState, hlower, hupper]]
        congr 1
        omega
      · simp [relocateActiveState, hlower, hupper]
    · simp [relocateActiveState, hlower]

theorem run_selectiveRelocatedCall
    {whole source : NPOracleProgram}
    {pcOffset registerOffset accumulator returnPc maximumBits calleeFuel
      calleeOutput extraFuel finalOutput : ℕ}
    {machine : NPOracleState}
    (hat :
      ProgramCallableAt whole source pcOffset registerOffset accumulator
        returnPc)
    (haccumulator : accumulator < registerOffset)
    (hpc : machine.pc = pcOffset)
    (hcallee : ∀ entry : NPOracleState, entry.pc = 0 →
      entry.registers 0 = machine.registers registerOffset →
      runNPOracleProgram source maximumBits calleeFuel entry =
        some calleeOutput)
    (haccumulatorZero : machine.registers accumulator = 0)
    (hpairBits :
      natBitLength (Nat.pair 0 calleeOutput) ≤ maximumBits)
    (hreturn : ∀ haltState : NPOracleState,
      runNPOracleProgram whole maximumBits extraFuel
        (((relocateState pcOffset registerOffset machine.registers
            haltState).write accumulator
              (Nat.pair 0 calleeOutput)).jump returnPc) =
        some finalOutput) :
    runNPOracleProgram whole maximumBits (calleeFuel + extraFuel) machine =
      some finalOutput := by
  rw [relocateActiveState_self pcOffset registerOffset
    (programRegisterSpan source) machine hpc]
  refine run_callable_active (span := programRegisterSpan source)
    machine.registers haccumulator (le_refl _) hat
    (hcallee _ rfl (by simp)) ?_ ?_
  · rw [haccumulatorZero]
    exact hpairBits
  · intro haltState unused
    rw [Nat.add_comm unused extraFuel, haccumulatorZero]
    exact run_fuel_add (hreturn haltState) unused

/-! ## 5. The reverse fold

Interpreter resources on this level are data dependent, so the fold's clock and
register-width envelope are defined by the same recursion as its output. -/

/-- Interpreter fuel of the reverse fold: fourteen controller steps, one
relocated append, and four controller steps per retained candidate. -/
def selectiveCountCasesFoldFuel {n : ℕ} :
    SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      14 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (4 +
            selectiveCountCasesFoldFuel
              (selectiveOr state value accumulated).state
              (selectiveOr state value accumulated).output rest))

/-- Largest value the reverse fold ever writes.  Every intermediate register is
a component of one of these three, so `natBitLength` of this bound is a legal
register width for the whole pass. -/
def selectiveCountCasesFoldWorkBound {n : ℕ} :
    SelectiveState n → ℕ → List ℕ → ℕ
  | state, accumulated, [] =>
      Nat.pair (selectiveStateCode state) accumulated
  | state, accumulated, value :: rest =>
      max (selectiveCountCasesSpineCode (value :: rest)) <|
        max
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.or value accumulated))) <|
          max
            (Nat.pair 0
              (selectiveWireCode (selectiveOr state value accumulated))) <|
            selectiveCountCasesFoldWorkBound
              (selectiveOr state value accumulated).state
              (selectiveOr state value accumulated).output rest

set_option maxHeartbeats 1600000 in
-- One fold iteration is eighteen controller steps around one relocated append,
-- so its trace threads a fourteen-write register chain before the call.
private theorem run_selectiveCountCasesFoldStep {n : ℕ}
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
    (hpc : machine.pc = 42)
    (hstate : machine.registers 2 = selectiveStateCode state)
    (harity : machine.registers 6 = n)
    (hspine :
      machine.registers 20 = selectiveCountCasesSpineCode (value :: rest))
    (haccumulated : machine.registers 22 = accumulated)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 42 →
      resumed.registers 0 =
        selectiveWireCode (selectiveOr state value accumulated) →
      resumed.registers 2 =
        selectiveStateCode (selectiveOr state value accumulated).state →
      resumed.registers 6 = n →
      resumed.registers 20 = selectiveCountCasesSpineCode rest →
      resumed.registers 22 = (selectiveOr state value accumulated).output →
      runNPOracleProgram totalSelectiveCountCasesProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram totalSelectiveCountCasesProgram maximumBits
        (14 + (emitFuel + (4 + extraFuel))) machine =
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
  -- register-width facts for every value the iteration writes
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
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le _)).trans hvalueBits
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
  have houtputWireBits :
      natBitLength (selectiveWireCode (selectiveOr state value accumulated)) ≤
        maximumBits :=
    (natBitLength_mono (Nat.right_le_pair 0 _)).trans hwireBits
  have hnextStateBits :
      natBitLength
          (selectiveStateCode (selectiveOr state value accumulated).state) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans houtputWireBits
    rw [hwireForm]
    exact Nat.left_le_pair _ _
  have hnextOutputBits :
      natBitLength (selectiveOr state value accumulated).output ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans houtputWireBits
    rw [hwireForm]
    exact Nat.right_le_pair _ _
  have hemitOutput :
      selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.or value accumulated)) =
        selectiveWireCode (selectiveOr state value accumulated) :=
    selectiveEmitOutput_eq_wireCode state (.or value accumulated) hordered
  have hcalleeBits :
      selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.or value accumulated)) ≤
        maximumBits := by
    unfold selectiveEmitBits selectiveEmitWorkBound
    rcases Nat.le_total
        (selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.or value accumulated)))
        (selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.or value accumulated))) with
      hle | hle
    · rw [max_eq_right hle, hemitOutput]
      exact houtputWireBits
    · rw [max_eq_left hle]
      exact hinputBits
  -- the trace
  have hspineNonzero : machine.registers 20 ≠ 0 := by
    rw [hspine, hspineForm]
    have hone := Nat.left_le_pair 1 (Nat.pair value (selectiveCountCasesSpineCode rest))
    omega
  rw [show 14 + (emitFuel + (4 + extraFuel)) =
    (13 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 42) rfl) hpc]
  rw [if_neg hspineNonzero]
  rw [show 13 + (emitFuel + (4 + extraFuel)) =
    (12 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair value (selectiveCountCasesSpineCode rest))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.jump, hspine, hspineForm]) hconsBits]
  rw [show 12 + (emitFuel + (4 + extraFuel)) =
    (11 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_unpairLeft_instruction (value := value)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 44) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
  rw [show 11 + (emitFuel + (4 + extraFuel)) =
    (10 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_unpairRight_instruction
    (value := selectiveCountCasesSpineCode rest)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 45) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
  rw [show 10 + (emitFuel + (4 + extraFuel)) =
    (9 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_add_instruction (value := n + value)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 46) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity])
    hleftChildBits]
  rw [show 9 + (emitFuel + (4 + extraFuel)) =
    (8 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_add_instruction (value := n + accumulated)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 47) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity, haccumulated])
    hrightChildBits]
  rw [show 8 + (emitFuel + (4 + extraFuel)) =
    (7 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair (n + value) (n + accumulated))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 48) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
  rw [show 7 + (emitFuel + (4 + extraFuel)) =
    (6 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 49) rfl) rfl hfourBits]
  rw [show 6 + (emitFuel + (4 + extraFuel)) =
    (5 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.or value accumulated))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 50) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 5 + (emitFuel + (4 + extraFuel)) =
    (4 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 51) rfl) rfl]
  simp only [ite_self]
  rw [show 4 + (emitFuel + (4 + extraFuel)) =
    (3 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected)
        (rawCircuitNodeCode (n := n) (.or value accumulated)))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 53) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstate, hemitInput])
    hinputBits]
  rw [show 3 + (emitFuel + (4 + extraFuel)) =
    (2 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 54) rfl) rfl hzeroBits]
  rw [show 2 + (emitFuel + (4 + extraFuel)) =
    (1 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 55) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (4 + extraFuel)) =
    (emitFuel + (4 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 56) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (selectiveOr state value accumulated))
    totalSelectiveCountCasesProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro entry hentryPc hentryInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state (.or value accumulated) hordered
        entry hentryPc ?_) hcalleeBits
    rw [hentryInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    rw [show (4 : ℕ) + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (selectiveOr state value accumulated))
      (totalSelectiveCountCasesProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) houtputWireBits]
    rw [show (3 : ℕ) + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode (selectiveOr state value accumulated).state)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 58) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      hnextStateBits]
    rw [show (2 : ℕ) + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := (selectiveOr state value accumulated).output)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      hnextOutputBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (totalSelectiveCountCasesProgram_controllerAt (pc := 60) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, harity]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState]
    · simp [NPOracleState.write, NPOracleState.jump]

set_option maxHeartbeats 800000 in
-- The reverse pass is one induction on the retained spine; each step is
-- discharged by the fold-step trace above.
private theorem run_selectiveCountCasesFoldLoop {n : ℕ}
    (values : List ℕ) (state : SelectiveState n) (accumulated : ℕ)
    (hordered : selectiveStateOrdered state) (maximumBits : ℕ)
    (hbits :
      natBitLength
          (selectiveCountCasesFoldWorkBound state accumulated values) ≤
        maximumBits)
    (machine : NPOracleState) (hpc : machine.pc = 42)
    (hwire :
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated)
    (hstate : machine.registers 2 = selectiveStateCode state)
    (harity : machine.registers 6 = n)
    (hspine : machine.registers 20 = selectiveCountCasesSpineCode values)
    (haccumulated : machine.registers 22 = accumulated) :
    runNPOracleProgram totalSelectiveCountCasesProgram maximumBits
        (selectiveCountCasesFoldFuel state accumulated values) machine =
      some
        (selectiveWireCode
          (selectiveCountCasesFold state accumulated values)) := by
  induction values generalizing state accumulated machine with
  | nil =>
      have hfuel :
          selectiveCountCasesFoldFuel state accumulated ([] : List ℕ) =
            (0 + 1) + 1 := rfl
      have hfoldNil :
          selectiveWireCode
              (selectiveCountCasesFold state accumulated ([] : List ℕ)) =
            Nat.pair (selectiveStateCode state) accumulated := rfl
      rw [hfuel]
      rw [run_branchZero_instruction
        (totalSelectiveCountCasesProgram_controllerAt (pc := 42) rfl) hpc]
      rw [if_pos (by rw [hspine]; rfl)]
      refine run_halt_instruction (fuel := 0)
        (totalSelectiveCountCasesProgram_controllerAt (pc := 52) rfl) rfl ?_ ?_
      · rw [hfoldNil]
        exact hwire
      · rw [hfoldNil]
        exact hbits
  | cons value rest ih =>
      have hfuel :
          selectiveCountCasesFoldFuel state accumulated (value :: rest) =
            14 +
              (selectiveEmitFuel (state.target - state.next)
                  (selectiveSelectedCode state.selected) +
                (4 +
                  selectiveCountCasesFoldFuel
                    (selectiveOr state value accumulated).state
                    (selectiveOr state value accumulated).output rest)) := rfl
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
      have hspineBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbits
      have hbitsTail :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbits
      have hinputBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTail
      have hbitsTailTwo :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTail
      have hwireBits :=
        (natBitLength_mono (Nat.le_max_left _ _)).trans hbitsTailTwo
      have hrecBits :=
        (natBitLength_mono (Nat.le_max_right _ _)).trans hbitsTailTwo
      rw [hfuel]
      refine run_selectiveCountCasesFoldStep state accumulated value rest
        hordered maximumBits _ _ _ machine rfl hspineBits hinputBits hwireBits
        hpc hstate harity hspine haccumulated ?_
      intro resumed hresumedPc hresumedWire hresumedState hresumedArity
        hresumedSpine hresumedAccumulated
      exact ih _ _
        (selectiveState_emit_ordered state (.or value accumulated) hordered)
        hrecBits _ hresumedPc hresumedWire hresumedState hresumedArity
        hresumedSpine hresumedAccumulated

/-! ## 6. The forward candidate pass

The fixed-count sub-compiler's own run is the single named premise of this
module.  It is packaged as a runner: interpreter resources as functions of the
compiled request only, and a run at an arbitrary entry state, because each call
starts on whatever registers the previous call left in the callee's frame. -/

theorem natBitLength_pair_left {left right maximumBits : ℕ}
    (hbits : natBitLength (Nat.pair left right) ≤ maximumBits) :
    natBitLength left ≤ maximumBits :=
  (natBitLength_mono (Nat.left_le_pair left right)).trans hbits

theorem natBitLength_pair_right {left right maximumBits : ℕ}
    (hbits : natBitLength (Nat.pair left right) ≤ maximumBits) :
    natBitLength right ≤ maximumBits :=
  (natBitLength_mono (Nat.right_le_pair left right)).trans hbits

set_option maxHeartbeats 1600000 in
-- One candidate iteration builds the callee's eight-field request in place,
-- runs the relocated sub-compiler, and conses its output onto the spine.
private theorem run_selectiveCountCasesForwardStep
    (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) (spine : List ℕ)
    (maximumBits calleeFuel extraFuel finalOutput remaining : ℕ)
    (machine : NPOracleState) (hordered : selectiveStateOrdered state)
    (hcalleeFuel : calleeFuel = runner.fuel state candidate)
    (hcalleeBits : runner.bits state candidate ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveFixedCountInput (selectiveStateCode state)
            (encodeTaggedList outputs) (structuralInputArity width bound)
            (structuralRowWidth width bound) (width + bound + 1) width count
            bound candidate.val) ≤
        maximumBits)
    (hheadBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileTableFixedCount outputs width count bound state
                candidate))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveCompileTableFixedCount outputs width count bound state
                candidate).output :: spine)) ≤
        maximumBits)
    (hremainingBound : remaining ≤ bound) (hremainingNonzero : remaining ≠ 0)
    (hpc : machine.pc = 17)
    (hstate : machine.registers 2 = selectiveStateCode state)
    (htable : machine.registers 4 = encodeTaggedList outputs)
    (harity : machine.registers 6 = structuralInputArity width bound)
    (hrowWidth : machine.registers 8 = structuralRowWidth width bound)
    (hfieldLimit : machine.registers 10 = width + bound + 1)
    (hwidth : machine.registers 12 = width)
    (hcount : machine.registers 14 = count)
    (hbound : machine.registers 16 = bound)
    (hprocessed : machine.registers 18 = candidate.val)
    (hremaining : machine.registers 19 = remaining)
    (hspine : machine.registers 20 = selectiveCountCasesSpineCode spine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 17 →
      resumed.registers 2 =
        selectiveStateCode
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state →
      resumed.registers 4 = encodeTaggedList outputs →
      resumed.registers 6 = structuralInputArity width bound →
      resumed.registers 8 = structuralRowWidth width bound →
      resumed.registers 10 = width + bound + 1 →
      resumed.registers 12 = width →
      resumed.registers 14 = count →
      resumed.registers 16 = bound →
      resumed.registers 18 = candidate.val + 1 →
      resumed.registers 19 = Nat.pred remaining →
      resumed.registers 20 =
        selectiveCountCasesSpineCode
          ((selectiveCompileTableFixedCount outputs width count bound state
              candidate).output :: spine) →
      runNPOracleProgram totalSelectiveCountCasesProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram totalSelectiveCountCasesProgram maximumBits
        (12 + (calleeFuel + (9 + extraFuel))) machine =
      some finalOutput := by
  have hrequestFlat := hrequestBits
  simp only [selectiveFixedCountInput] at hrequestFlat
  have hfield1 := natBitLength_pair_right hrequestFlat
  have hfield2 := natBitLength_pair_right hfield1
  have hfield3 := natBitLength_pair_right hfield2
  have hfield4 := natBitLength_pair_right hfield3
  have hfield5 := natBitLength_pair_right hfield4
  have hfield6 := natBitLength_pair_right hfield5
  have hfield7 := natBitLength_pair_right hfield6
  have hboundBits := natBitLength_pair_left hfield7
  have hheadFlat := natBitLength_pair_right hheadBits
  have hheadParts := hheadFlat
  simp only [selectiveWireCode] at hheadParts
  have hheadStateBits := natBitLength_pair_left hheadParts
  have hheadOutputBits := natBitLength_pair_right hheadParts
  have hspineFlat := hspineBits
  simp only [selectiveCountCasesSpineCode] at hspineFlat
  have honeBits := natBitLength_pair_left hspineFlat
  have hconsBits := natBitLength_pair_right hspineFlat
  have hzeroBits : natBitLength 0 ≤ maximumBits :=
    (natBitLength_mono (Nat.zero_le 1)).trans honeBits
  have hnextProcessedBits :
      natBitLength (candidate.val + 1) ≤ maximumBits :=
    (natBitLength_mono candidate.isLt).trans hboundBits
  have hnextRemainingBits :
      natBitLength (Nat.pred remaining) ≤ maximumBits :=
    (natBitLength_mono (Nat.pred_le remaining |>.trans hremainingBound)).trans
      hboundBits
  rw [show 12 + (calleeFuel + (9 + extraFuel)) =
    (11 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 17) rfl) hpc]
  rw [if_neg (by rw [hremaining]; exact hremainingNonzero)]
  rw [show 11 + (calleeFuel + (9 + extraFuel)) =
    (10 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction (value := Nat.pair bound candidate.val)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 18) rfl) rfl
    (by simp [NPOracleState.jump, hbound, hprocessed]) hfield7]
  rw [show 10 + (calleeFuel + (9 + extraFuel)) =
    (9 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := Nat.pair count (Nat.pair bound candidate.val))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcount]) hfield6]
  rw [show 9 + (calleeFuel + (9 + extraFuel)) =
    (8 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair width (Nat.pair count (Nat.pair bound candidate.val)))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 20) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfield5]
  rw [show 8 + (calleeFuel + (9 + extraFuel)) =
    (7 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (width + bound + 1)
        (Nat.pair width (Nat.pair count (Nat.pair bound candidate.val))))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 21) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hfield4]
  rw [show 7 + (calleeFuel + (9 + extraFuel)) =
    (6 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (structuralRowWidth width bound)
        (Nat.pair (width + bound + 1)
          (Nat.pair width (Nat.pair count (Nat.pair bound candidate.val)))))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 22) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowWidth]) hfield3]
  rw [show 6 + (calleeFuel + (9 + extraFuel)) =
    (5 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (structuralInputArity width bound)
        (Nat.pair (structuralRowWidth width bound)
          (Nat.pair (width + bound + 1)
            (Nat.pair width
              (Nat.pair count (Nat.pair bound candidate.val))))))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 23) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) hfield2]
  rw [show 5 + (calleeFuel + (9 + extraFuel)) =
    (4 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeTaggedList outputs)
        (Nat.pair (structuralInputArity width bound)
          (Nat.pair (structuralRowWidth width bound)
            (Nat.pair (width + bound + 1)
              (Nat.pair width
                (Nat.pair count (Nat.pair bound candidate.val)))))))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 24) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, htable]) hfield1]
  rw [show 4 + (calleeFuel + (9 + extraFuel)) =
    (3 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveFixedCountInput (selectiveStateCode state)
        (encodeTaggedList outputs) (structuralInputArity width bound)
        (structuralRowWidth width bound) (width + bound + 1) width count bound
        candidate.val)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 25) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstate,
        selectiveFixedCountInput])
    hrequestBits]
  rw [show 3 + (calleeFuel + (9 + extraFuel)) =
    (2 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 26) rfl) rfl hzeroBits]
  rw [show 2 + (calleeFuel + (9 + extraFuel)) =
    (1 + (calleeFuel + (9 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 27) rfl) rfl hzeroBits]
  rw [show 1 + (calleeFuel + (9 + extraFuel)) =
    (calleeFuel + (9 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 28) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := totalSelectiveFixedCountProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileTableFixedCount outputs width count bound state
          candidate))
    totalSelectiveCountCasesProgram_fixedCountCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro entry hentryPc hentryInput
    refine run_bits_mono
      (runner.executes state candidate hordered entry hentryPc ?_) hcalleeBits
    rw [hentryInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hheadBits
  · intro haltState
    rw [show (9 : ℕ) + extraFuel = (8 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate))
      (totalSelectiveCountCasesProgram_controllerAt (pc := 29) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hheadFlat]
    rw [show (8 : ℕ) + extraFuel = (7 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).state)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 30) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hheadStateBits]
    rw [show (7 : ℕ) + extraFuel = (6 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveCompileTableFixedCount outputs width count bound state
          candidate).output)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 31) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hheadOutputBits]
    rw [show (6 : ℕ) + extraFuel = (5 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair
          (selectiveCompileTableFixedCount outputs width count bound state
            candidate).output (selectiveCountCasesSpineCode spine))
      (totalSelectiveCountCasesProgram_controllerAt (pc := 32) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine])
      hconsBits]
    rw [show (5 : ℕ) + extraFuel = (4 + extraFuel) + 1 by omega]
    rw [run_set_instruction
      (totalSelectiveCountCasesProgram_controllerAt (pc := 33) rfl) rfl honeBits]
    rw [show (4 : ℕ) + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_pair_instruction
      (value :=
        selectiveCountCasesSpineCode
          ((selectiveCompileTableFixedCount outputs width count bound state
              candidate).output :: spine))
      (totalSelectiveCountCasesProgram_controllerAt (pc := 34) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump,
          selectiveCountCasesSpineCode])
      hspineBits]
    rw [show (3 : ℕ) + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_increment_instruction (value := candidate.val + 1)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 35) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hprocessed])
      hnextProcessedBits]
    rw [show (2 : ℕ) + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_decrement_instruction (value := Nat.pred remaining)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 36) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hremaining])
      hnextRemainingBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (totalSelectiveCountCasesProgram_controllerAt (pc := 37) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, htable]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, harity]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hrowWidth]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hfieldLimit]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hwidth]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hcount]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hbound]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]

set_option maxHeartbeats 1600000 in
-- The candidate loop's exit emits the source compiler's explicit `false` base
-- case and hands the retained spine to the reverse pass.
private theorem run_selectiveCountCasesBaseStep {n : ℕ}
    (state : SelectiveState n) (spine : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits emitFuel extraFuel finalOutput : ℕ)
    (machine : NPOracleState)
    (hemitFuel :
      emitFuel =
        selectiveEmitFuel (state.target - state.next)
          (selectiveSelectedCode state.selected))
    (hinputBits :
      natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := n) (.const false))) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0 (selectiveWireCode (selectiveConst state false))) ≤
        maximumBits)
    (hpc : machine.pc = 17)
    (hstate : machine.registers 2 = selectiveStateCode state)
    (harity : machine.registers 6 = n)
    (hremaining : machine.registers 19 = 0)
    (hspine : machine.registers 20 = selectiveCountCasesSpineCode spine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 42 →
      resumed.registers 0 = selectiveWireCode (selectiveConst state false) →
      resumed.registers 2 =
        selectiveStateCode (selectiveConst state false).state →
      resumed.registers 6 = n →
      resumed.registers 20 = selectiveCountCasesSpineCode spine →
      resumed.registers 22 = (selectiveConst state false).output →
      runNPOracleProgram totalSelectiveCountCasesProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram totalSelectiveCountCasesProgram maximumBits
        (9 + (emitFuel + (4 + extraFuel))) machine =
      some finalOutput := by
  have hnodeCode :
      rawCircuitNodeCode (n := n) (.const false) = Nat.pair 0 0 := rfl
  have hemitInput :
      selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.const false)) =
        Nat.pair (selectiveStateCode state)
          (rawCircuitNodeCode (n := n) (.const false)) := rfl
  have hwireForm :
      selectiveWireCode (selectiveConst state false) =
        Nat.pair (selectiveStateCode (selectiveConst state false).state)
          (selectiveConst state false).output := rfl
  have hcodeBits :
      natBitLength (rawCircuitNodeCode (n := n) (.const false)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hinputBits
    rw [hemitInput]
    exact Nat.right_le_pair _ _
  have hzeroBits : natBitLength 0 ≤ maximumBits := by
    rw [hnodeCode] at hcodeBits
    exact natBitLength_pair_left hcodeBits
  have houtputWireBits :
      natBitLength (selectiveWireCode (selectiveConst state false)) ≤
        maximumBits :=
    natBitLength_pair_right hwireBits
  have hnextStateBits :
      natBitLength
          (selectiveStateCode (selectiveConst state false).state) ≤
        maximumBits := by
    rw [hwireForm] at houtputWireBits
    exact natBitLength_pair_left houtputWireBits
  have hnextOutputBits :
      natBitLength (selectiveConst state false).output ≤ maximumBits := by
    rw [hwireForm] at houtputWireBits
    exact natBitLength_pair_right houtputWireBits
  have hemitOutput :
      selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.const false)) =
        selectiveWireCode (selectiveConst state false) :=
    selectiveEmitOutput_eq_wireCode state (.const false) hordered
  have hcalleeBits :
      selectiveEmitBits (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.const false)) ≤
        maximumBits := by
    unfold selectiveEmitBits selectiveEmitWorkBound
    rcases Nat.le_total
        (selectiveEmitInput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.const false)))
        (selectiveEmitOutput (state.target - state.next) state.next
          (selectiveSelectedCode state.selected)
          (rawCircuitNodeCode (n := n) (.const false))) with hle | hle
    · rw [max_eq_right hle, hemitOutput]
      exact natBitLength_pair_right hwireBits
    · rw [max_eq_left hle]
      exact hinputBits
  rw [show 9 + (emitFuel + (4 + extraFuel)) =
    (8 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 17) rfl) hpc]
  rw [if_pos hremaining]
  rw [show 8 + (emitFuel + (4 + extraFuel)) =
    (7 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 38) rfl) rfl hzeroBits]
  rw [show 7 + (emitFuel + (4 + extraFuel)) =
    (6 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 39) rfl) rfl hzeroBits]
  rw [show 6 + (emitFuel + (4 + extraFuel)) =
    (5 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value := rawCircuitNodeCode (n := n) (.const false))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 40) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCode]) hcodeBits]
  rw [show 5 + (emitFuel + (4 + extraFuel)) =
    (4 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 41) rfl) rfl]
  simp only [ite_self]
  rw [show 4 + (emitFuel + (4 + extraFuel)) =
    (3 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected)
        (rawCircuitNodeCode (n := n) (.const false)))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 53) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstate, hemitInput])
    hinputBits]
  rw [show 3 + (emitFuel + (4 + extraFuel)) =
    (2 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 54) rfl) rfl hzeroBits]
  rw [show 2 + (emitFuel + (4 + extraFuel)) =
    (1 + (emitFuel + (4 + extraFuel))) + 1 by omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 55) rfl) rfl hzeroBits]
  rw [show 1 + (emitFuel + (4 + extraFuel)) =
    (emitFuel + (4 + extraFuel)) + 1 by omega]
  rw [run_branchZero_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 56) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (selectiveConst state false))
    totalSelectiveCountCasesProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro entry hentryPc hentryInput
    refine run_bits_mono
      (run_selectiveEmitProgram_eq_emit state (.const false) hordered entry
        hentryPc ?_) hcalleeBits
    rw [hentryInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro haltState
    rw [show (4 : ℕ) + extraFuel = (3 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := selectiveWireCode (selectiveConst state false))
      (totalSelectiveCountCasesProgram_controllerAt (pc := 57) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) houtputWireBits]
    rw [show (3 : ℕ) + extraFuel = (2 + extraFuel) + 1 by omega]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (selectiveConst state false).state)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 58) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      hnextStateBits]
    rw [show (2 : ℕ) + extraFuel = (1 + extraFuel) + 1 by omega]
    rw [run_unpairRight_instruction
      (value := (selectiveConst state false).output)
      (totalSelectiveCountCasesProgram_controllerAt (pc := 59) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hwireForm])
      hnextOutputBits]
    rw [show (1 : ℕ) + extraFuel = extraFuel + 1 by omega]
    rw [run_branchZero_instruction
      (totalSelectiveCountCasesProgram_controllerAt (pc := 60) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl ?_ ?_ ?_ ?_ ?_
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, harity]
    · simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine]
    · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 7. The candidate loop -/

/-- The controller visits candidate node counts in ascending order from a
fixed start. -/
private def SelectiveCandidatesFrom {bound : ℕ} : ℕ → List (Fin bound) → Prop
  | _, [] => True
  | start, candidate :: rest =>
      candidate.val = start ∧ SelectiveCandidatesFrom (start + 1) rest

private theorem selectiveCandidatesFrom_ofFn {bound : ℕ} :
    ∀ (length start : ℕ) (index : Fin length → Fin bound),
      (∀ position : Fin length,
        (index position).val = start + position.val) →
      SelectiveCandidatesFrom start (List.ofFn index)
  | 0, start, index, _ => by
      simp only [List.ofFn_zero]
      exact trivial
  | length + 1, start, index, hindex => by
      rw [List.ofFn_succ]
      refine ⟨by simpa using hindex 0, ?_⟩
      refine selectiveCandidatesFrom_ofFn length (start + 1)
        (fun position => index position.succ) ?_
      intro position
      have hposition := hindex position.succ
      simp only [Fin.val_succ] at hposition
      omega

/-- Interpreter fuel of the whole controller from the candidate loop head. -/
private def selectiveCountCasesForwardFuel (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      List ℕ → ℕ
  | state, [], spine =>
      9 +
        (selectiveEmitFuel (state.target - state.next)
            (selectiveSelectedCode state.selected) +
          (4 +
            selectiveCountCasesFoldFuel (selectiveConst state false).state
              (selectiveConst state false).output spine))
  | state, candidate :: rest, spine =>
      12 +
        (runner.fuel state candidate +
          (9 +
            selectiveCountCasesForwardFuel outputs width count bound runner
              (selectiveCompileTableFixedCount outputs width count bound state
                candidate).state rest
              ((selectiveCompileTableFixedCount outputs width count bound state
                candidate).output :: spine)))

/-- Register width of the whole controller from the candidate loop head. -/
private def selectiveCountCasesForwardBits (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound) :
    SelectiveState (descriptionWidth width bound) → List (Fin bound) →
      List ℕ → ℕ
  | state, [], spine =>
      max
        (natBitLength
          (selectiveEmitInput (state.target - state.next) state.next
            (selectiveSelectedCode state.selected)
            (rawCircuitNodeCode (n := descriptionWidth width bound)
              (.const false)))) <|
        max
          (natBitLength
            (Nat.pair 0 (selectiveWireCode (selectiveConst state false)))) <|
          natBitLength
            (selectiveCountCasesFoldWorkBound (selectiveConst state false).state
              (selectiveConst state false).output spine)
  | state, candidate :: rest, spine =>
      max (runner.bits state candidate) <|
        max
          (natBitLength
            (selectiveFixedCountInput (selectiveStateCode state)
              (encodeTaggedList outputs) (structuralInputArity width bound)
              (structuralRowWidth width bound) (width + bound + 1) width count
              bound candidate.val)) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveCompileTableFixedCount outputs width count bound
                    state candidate)))) <|
            max
              (natBitLength
                (selectiveCountCasesSpineCode
                  ((selectiveCompileTableFixedCount outputs width count bound
                      state candidate).output :: spine))) <|
              selectiveCountCasesForwardBits outputs width count bound runner
                (selectiveCompileTableFixedCount outputs width count bound state
                  candidate).state rest
                ((selectiveCompileTableFixedCount outputs width count bound
                    state candidate).output :: spine)

/-- Compiler wire the controller produces from the candidate loop head. -/
private def selectiveCountCasesForwardOutput (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidates : List (Fin bound)) (spine : List ℕ) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveCountCasesFold
    (selectiveConst
      (selectiveCountCasesHeads outputs width count bound state
        candidates).state false).state
    (selectiveConst
      (selectiveCountCasesHeads outputs width count bound state
        candidates).state false).output
    ((selectiveCountCasesHeads outputs width count bound state
      candidates).values.reverse ++ spine)

private theorem selectiveCountCasesForwardOutput_cons (outputs : List ℕ)
    (width count bound : ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (candidate : Fin bound) (rest : List (Fin bound)) (spine : List ℕ) :
    selectiveCountCasesForwardOutput outputs width count bound state
        (candidate :: rest) spine =
      selectiveCountCasesForwardOutput outputs width count bound
        (selectiveCompileTableFixedCount outputs width count bound state
          candidate).state rest
        ((selectiveCompileTableFixedCount outputs width count bound state
          candidate).output :: spine) := by
  simp only [selectiveCountCasesForwardOutput, selectiveCountCasesHeads,
    List.reverse_cons, List.append_assoc, List.singleton_append]

set_option maxHeartbeats 1000000 in
-- The forward pass is one induction on the remaining candidates; its exit
-- chains the base append into the reverse pass.
private theorem run_selectiveCountCasesForwardLoop (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (candidates : List (Fin bound)) (processed : ℕ)
    (state : SelectiveState (descriptionWidth width bound)) (spine : List ℕ)
    (maximumBits : ℕ) (machine : NPOracleState)
    (hcandidates : SelectiveCandidatesFrom processed candidates)
    (hlength : processed + candidates.length = bound)
    (hordered : selectiveStateOrdered state)
    (hbits :
      selectiveCountCasesForwardBits outputs width count bound runner state
          candidates spine ≤
        maximumBits)
    (hpc : machine.pc = 17)
    (hstate : machine.registers 2 = selectiveStateCode state)
    (htable : machine.registers 4 = encodeTaggedList outputs)
    (harity : machine.registers 6 = structuralInputArity width bound)
    (hrowWidth : machine.registers 8 = structuralRowWidth width bound)
    (hfieldLimit : machine.registers 10 = width + bound + 1)
    (hwidth : machine.registers 12 = width)
    (hcount : machine.registers 14 = count)
    (hbound : machine.registers 16 = bound)
    (hprocessed : machine.registers 18 = processed)
    (hremaining : machine.registers 19 = candidates.length)
    (hspine : machine.registers 20 = selectiveCountCasesSpineCode spine) :
    runNPOracleProgram totalSelectiveCountCasesProgram maximumBits
        (selectiveCountCasesForwardFuel outputs width count bound runner state
          candidates spine) machine =
      some
        (selectiveWireCode
          (selectiveCountCasesForwardOutput outputs width count bound state
            candidates spine)) := by
  induction candidates generalizing processed state spine machine with
  | nil =>
      have hfuel :
          selectiveCountCasesForwardFuel outputs width count bound runner state
              [] spine =
            9 +
              (selectiveEmitFuel (state.target - state.next)
                  (selectiveSelectedCode state.selected) +
                (4 +
                  selectiveCountCasesFoldFuel
                    (selectiveConst state false).state
                    (selectiveConst state false).output spine)) := rfl
      have hbitsNil :
          selectiveCountCasesForwardBits outputs width count bound runner state
              [] spine =
            max
              (natBitLength
                (selectiveEmitInput (state.target - state.next) state.next
                  (selectiveSelectedCode state.selected)
                  (rawCircuitNodeCode (n := descriptionWidth width bound)
                    (.const false))))
              (max
                (natBitLength
                  (Nat.pair 0
                    (selectiveWireCode (selectiveConst state false))))
                (natBitLength
                  (selectiveCountCasesFoldWorkBound
                    (selectiveConst state false).state
                    (selectiveConst state false).output spine))) := rfl
      rw [hbitsNil] at hbits
      have hinputBits := (Nat.le_max_left _ _).trans hbits
      have hbitsTail := (Nat.le_max_right _ _).trans hbits
      have hwireBits := (Nat.le_max_left _ _).trans hbitsTail
      have hfoldBits := (Nat.le_max_right _ _).trans hbitsTail
      rw [hfuel]
      refine run_selectiveCountCasesBaseStep state spine hordered maximumBits
        _ _ _ machine rfl hinputBits hwireBits hpc hstate harity
        (by rw [hremaining]; rfl) hspine ?_
      intro resumed hresumedPc hresumedWire hresumedState hresumedArity
        hresumedSpine hresumedAccumulated
      exact run_selectiveCountCasesFoldLoop spine
        (selectiveConst state false).state (selectiveConst state false).output
        (selectiveState_emit_ordered state (.const false) hordered) maximumBits
        hfoldBits resumed hresumedPc hresumedWire hresumedState hresumedArity
        hresumedSpine hresumedAccumulated
  | cons candidate rest ih =>
      have hfuel :
          selectiveCountCasesForwardFuel outputs width count bound runner state
              (candidate :: rest) spine =
            12 +
              (runner.fuel state candidate +
                (9 +
                  selectiveCountCasesForwardFuel outputs width count bound
                    runner
                    (selectiveCompileTableFixedCount outputs width count bound
                      state candidate).state rest
                    ((selectiveCompileTableFixedCount outputs width count bound
                      state candidate).output :: spine))) := rfl
      have hbitsCons :
          selectiveCountCasesForwardBits outputs width count bound runner state
              (candidate :: rest) spine =
            max (runner.bits state candidate)
              (max
                (natBitLength
                  (selectiveFixedCountInput (selectiveStateCode state)
                    (encodeTaggedList outputs)
                    (structuralInputArity width bound)
                    (structuralRowWidth width bound) (width + bound + 1) width
                    count bound candidate.val))
                (max
                  (natBitLength
                    (Nat.pair 0
                      (selectiveWireCode
                        (selectiveCompileTableFixedCount outputs width count
                          bound state candidate))))
                  (max
                    (natBitLength
                      (selectiveCountCasesSpineCode
                        ((selectiveCompileTableFixedCount outputs width count
                            bound state candidate).output :: spine)))
                    (selectiveCountCasesForwardBits outputs width count bound
                      runner
                      (selectiveCompileTableFixedCount outputs width count
                        bound state candidate).state rest
                      ((selectiveCompileTableFixedCount outputs width count
                          bound state candidate).output :: spine))))) := rfl
      rw [hbitsCons] at hbits
      have hcalleeBits := (Nat.le_max_left _ _).trans hbits
      have hbitsOne := (Nat.le_max_right _ _).trans hbits
      have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
      have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
      have hheadBits := (Nat.le_max_left _ _).trans hbitsTwo
      have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
      have hspineBits := (Nat.le_max_left _ _).trans hbitsThree
      have hrecBits := (Nat.le_max_right _ _).trans hbitsThree
      have hcandidateVal : candidate.val = processed := hcandidates.1
      simp only [List.length_cons] at hlength
      rw [hfuel, selectiveCountCasesForwardOutput_cons]
      refine run_selectiveCountCasesForwardStep outputs width count bound runner
        state candidate spine maximumBits _ _ _ (rest.length + 1) machine
        hordered rfl hcalleeBits hrequestBits hheadBits hspineBits (by omega) (by omega) hpc
        hstate htable harity hrowWidth hfieldLimit hwidth hcount hbound
        (by rw [hprocessed, hcandidateVal]) (by rw [hremaining]; rfl) hspine ?_
      intro resumed hresumedPc hresumedState hresumedTable hresumedArity
        hresumedRowWidth hresumedFieldLimit hresumedWidth hresumedCount
        hresumedBound hresumedProcessed hresumedRemaining hresumedSpine
      refine ih (processed + 1)
        (selectiveCompileTableFixedCount outputs width count bound state
          candidate).state
        ((selectiveCompileTableFixedCount outputs width count bound state
          candidate).output :: spine) resumed hcandidates.2 (by omega)
        (selectiveCompileTableFixedCount_ordered outputs width count bound state
          candidate hordered)
        hrecBits hresumedPc hresumedState hresumedTable hresumedArity
        hresumedRowWidth hresumedFieldLimit hresumedWidth hresumedCount
        hresumedBound (by rw [hresumedProcessed, hcandidateVal])
        (by rw [hresumedRemaining]; rfl) hresumedSpine

/-! ## 8. The whole 3052-instruction stream -/

/-- Register width of one whole nested-compiler run. -/
def selectiveCountCasesRunBits (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (index : ℕ) : ℕ :=
  max
    (natBitLength
      (structuralCompilerCoreInput outputs width count bound index))
    (selectiveCountCasesForwardBits outputs width count bound runner
      (SelectiveState.empty (descriptionWidth width bound)
        (index - structuralInputArity width bound))
      (List.ofFn id) [])

/-- Interpreter fuel of one whole nested-compiler run. -/
def selectiveCountCasesRunFuel (outputs : List ℕ) (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (index : ℕ) : ℕ :=
  17 +
    selectiveCountCasesForwardFuel outputs width count bound runner
      (SelectiveState.empty (descriptionWidth width bound)
        (index - structuralInputArity width bound))
      (List.ofFn id) []

set_option maxHeartbeats 1600000 in
-- The seventeen-step request parser feeds the two separately proved passes.
/-- **The nested structural compiler's run, modulo its fixed-count level.**
The 3052-instruction stream started on its own ABI frame returns exactly the
compiler wire the source compiler produces at that formula index. -/
theorem run_totalSelectiveCountCasesProgram (outputs : List ℕ)
    (width count bound : ℕ)
    (runner : SelectiveFixedCountProgramRunner totalSelectiveFixedCountProgram
      outputs width count bound)
    (machineInputLength index : ℕ) :
    runNPOracleProgram totalSelectiveCountCasesProgram
        (selectiveCountCasesRunBits outputs width count bound runner index)
        (selectiveCountCasesRunFuel outputs width count bound runner index)
        (initialNPOracleState machineInputLength
          (structuralCompilerCoreInput outputs width count bound index)) =
      some
        (selectiveWireCode
          (selectiveCompileTableBoundedOracleVerifier outputs width count bound
            (index - descriptionWidth width bound))) := by
  have hbits :
      natBitLength
          (structuralCompilerCoreInput outputs width count bound index) ≤
        selectiveCountCasesRunBits outputs width count bound runner index :=
    Nat.le_max_left _ _
  have hforwardBits :
      selectiveCountCasesForwardBits outputs width count bound runner
          (SelectiveState.empty (descriptionWidth width bound)
            (index - structuralInputArity width bound))
          (List.ofFn id) [] ≤
        selectiveCountCasesRunBits outputs width count bound runner index :=
    Nat.le_max_right _ _
  have hflat := hbits
  simp only [structuralCompilerCoreInput, selectiveCountCasesInput] at hflat
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
  have hboundBits := natBitLength_pair_right hsix
  have hzeroBits :
      natBitLength 0 ≤
        selectiveCountCasesRunBits outputs width count bound runner index :=
    (natBitLength_mono (Nat.zero_le _)).trans hboundBits
  have houtput :
      selectiveWireCode
          (selectiveCompileTableBoundedOracleVerifier outputs width count bound
            (index - descriptionWidth width bound)) =
        selectiveWireCode
          (selectiveCountCasesForwardOutput outputs width count bound
            (SelectiveState.empty (descriptionWidth width bound)
              (index - structuralInputArity width bound))
            (List.ofFn id) []) := by
    rw [selectiveCountCasesForwardOutput, List.append_nil,
      selectiveCompileTableBoundedOracleVerifier,
      selectiveCompileTableCountCases_eq_fold]
    rfl
  rw [houtput, selectiveCountCasesRunFuel]
  rw [show 17 +
      selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (16 +
      selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction
    (value :=
      selectiveStateCode
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 0) rfl) rfl
    (by
      simp [initialNPOracleState, structuralCompilerCoreInput,
        selectiveCountCasesInput]
      rfl)
    hstateBits]
  rw [show 16 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (15 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (encodeTaggedList outputs) <|
        Nat.pair (structuralInputArity width bound) <|
          Nat.pair (structuralRowWidth width bound) <|
            Nat.pair (width + bound + 1) <|
              Nat.pair width (Nat.pair count bound))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, initialNPOracleState,
        structuralCompilerCoreInput, selectiveCountCasesInput])
    hone]
  rw [show 15 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (14 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := encodeTaggedList outputs)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htableBits]
  rw [show 14 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (13 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (structuralInputArity width bound) <|
        Nat.pair (structuralRowWidth width bound) <|
          Nat.pair (width + bound + 1) <|
            Nat.pair width (Nat.pair count bound))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [show 13 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (12 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := structuralInputArity width bound)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [show 12 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (11 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (structuralRowWidth width bound) <|
        Nat.pair (width + bound + 1) <|
          Nat.pair width (Nat.pair count bound))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [show 11 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (10 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := structuralRowWidth width bound)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [show 10 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (9 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (width + bound + 1) (Nat.pair width (Nat.pair count bound)))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [show 9 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (8 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := width + bound + 1)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [show 8 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (7 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair count bound))
    (totalSelectiveCountCasesProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [show 7 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (6 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := width)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [show 6 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (5 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction (value := Nat.pair count bound)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsix]
  rw [show 5 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (4 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := count)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [show 4 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (3 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_unpairRight_instruction (value := bound)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hboundBits]
  rw [show 3 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (2 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 14) rfl) rfl hzeroBits]
  rw [show 2 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    (1 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) []) + 1 by
    omega]
  rw [run_copy_instruction (value := bound)
    (totalSelectiveCountCasesProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hboundBits]
  rw [show 1 + selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] =
    selectiveCountCasesForwardFuel outputs width count bound runner
        (SelectiveState.empty (descriptionWidth width bound)
          (index - structuralInputArity width bound)) (List.ofFn id) [] + 1 by
    omega]
  rw [run_set_instruction
    (totalSelectiveCountCasesProgram_controllerAt (pc := 16) rfl) rfl hzeroBits]
  refine run_selectiveCountCasesForwardLoop outputs width count bound runner
    (List.ofFn id) 0
    (SelectiveState.empty (descriptionWidth width bound)
      (index - structuralInputArity width bound))
    [] _ _ ?_ ?_ (by simp) hforwardBits rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact selectiveCandidatesFrom_ofFn bound 0 id (by simp)
  · simp
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
    rfl

end NearCubicWires.TotalSelectiveCountCasesProgram
