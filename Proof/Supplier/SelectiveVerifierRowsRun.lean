import Proof.Supplier.SelectiveFixedCountRun
import Proof.Supplier.SelectiveVerifierRowRun

/-!
# The verifier-row scheduler's run

`selectiveVerifierRowsProgram` is the `1762`-instruction stream that compiles
every verifier row of one candidate node count: a controller of `87`
instructions with two relocated callees, the `1657`-instruction single-row
compiler and the `18`-instruction append transition.

The controller derives two loop constants before it starts — the row count
`2 ^ width` by repeated doubling and the decision-table cursor `count * width`
by repeated addition — then walks the rows in ascending randomness order, one
relocated row compilation per row, with the row cursor and the decision cursor
advancing in lockstep.  Compiled rows stay on one private reverse spine, and the
exit emits the canonical `true` base case and folds that spine back into the
source compiler's right-associated conjunction.

This module executes that controller, discharging
`SelectiveFixedCountRun.SelectiveVerifierRowsRunner` from the level premises the
single-row compiler consumes.
-/

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralProjectionTable
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralTableCompiler
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

open private selectiveCompileTableVerifierRow_ordered from
  Proof.Supplier.SelectiveCountCasesRun

open private selectiveVerifierRowInput selectiveVerifierRowProgram
  selectiveVerifierRowProgram_length selectiveVerifierRowsControllerProgram
  selectiveVerifierRowsControllerProgram_length from
  Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

/-! ## 1. The row schedule, at the typed level -/

/-- The forward pass, in the order the controller accumulates it. -/
private def verifierRowsHeads {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    SelectiveState (descriptionWidth width bound) → List ℕ →
      SelectiveWireList (descriptionWidth width bound)
  | state, [] => { state := state, values := [] }
  | state, code :: rest =>
      let head :=
        selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount code
      let tail :=
        verifierRowsHeads outputs count nodeCount hnodeCount head.state rest
      { state := tail.state
        values := head.output :: tail.values }

/-- The forward pass with the reverse spine the controller actually carries. -/
private def verifierRowsPass {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    SelectiveState (descriptionWidth width bound) → List ℕ → List ℕ →
      SelectiveState (descriptionWidth width bound) × List ℕ
  | state, [], values => (state, values)
  | state, code :: rest, values =>
      verifierRowsPass outputs count nodeCount hnodeCount
        (selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount code).state rest
        ((selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount code).output :: values)

private theorem verifierRowsPass_eq {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    ∀ (codes : List ℕ)
      (state : SelectiveState (descriptionWidth width bound))
      (values : List ℕ),
      verifierRowsPass outputs count nodeCount hnodeCount state codes values =
        ((verifierRowsHeads outputs count nodeCount hnodeCount state
            codes).state,
          (verifierRowsHeads outputs count nodeCount hnodeCount state
            codes).values.reverse ++ values)
  | [], _, _ => rfl
  | code :: rest, state, values => by
      simp only [verifierRowsPass, verifierRowsHeads,
        verifierRowsPass_eq outputs count nodeCount hnodeCount rest _ _,
        List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **The controller's scheduling identity.**  The source compiler's
right-associated conjunction over the verifier rows is exactly the forward row
pass followed by the reverse `and` fold over the retained spine. -/
private theorem selectiveCompileTableVerifierRows_eq_fold {width bound : ℕ}
    (outputs : List ℕ) (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    ∀ (codes : List ℕ)
      (state : SelectiveState (descriptionWidth width bound)),
      selectiveCompileTableVerifierRows outputs width count bound nodeCount
          hnodeCount state codes =
        selectiveUnaryFold
          (selectiveConst
            (verifierRowsHeads outputs count nodeCount hnodeCount state
              codes).state true).state
          (selectiveConst
            (verifierRowsHeads outputs count nodeCount hnodeCount state
              codes).state true).output
          (verifierRowsHeads outputs count nodeCount hnodeCount state
            codes).values.reverse
  | [], _ => rfl
  | code :: rest, state => by
      simp only [selectiveCompileTableVerifierRows, verifierRowsHeads,
        List.reverse_cons]
      rw [selectiveUnaryFold_concat]
      rw [selectiveCompileTableVerifierRows_eq_fold outputs count nodeCount
        hnodeCount rest _]

private theorem verifierRowsHeads_ordered {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    ∀ (codes : List ℕ)
      (state : SelectiveState (descriptionWidth width bound)),
      selectiveStateOrdered state →
      selectiveStateOrdered
        (verifierRowsHeads outputs count nodeCount hnodeCount state
          codes).state
  | [], _, hordered => hordered
  | code :: rest, state, hordered =>
      verifierRowsHeads_ordered outputs count nodeCount hnodeCount rest _
        (selectiveCompileTableVerifierRow_ordered outputs width count bound
          state nodeCount hnodeCount code hordered)

/-- The randomness codes the row loop walks: ascending from one start. -/
private def VerifierRowsFrom : ℕ → List ℕ → Prop
  | _, [] => True
  | start, code :: rest => code = start ∧ VerifierRowsFrom (start + 1) rest

private theorem verifierRowsFrom_range' :
    ∀ (length start : ℕ), VerifierRowsFrom start (List.range' start length)
  | 0, _ => trivial
  | length + 1, start => by
      rw [List.range'_succ]
      exact ⟨rfl, verifierRowsFrom_range' length (start + 1)⟩

private theorem verifierRowsFrom_range (length : ℕ) :
    VerifierRowsFrom 0 (List.range length) := by
  rw [List.range_eq_range']
  exact verifierRowsFrom_range' length 0

/-! ## 2. Decoding the fixed 1762-instruction stream -/

private theorem selectiveVerifierRowsProgram_controllerAt {pc : ℕ}
    {instruction : NPOracleInstruction}
    (hlookup :
      (selectiveVerifierRowsControllerProgram 87 1744)[pc]? =
        some instruction) :
    selectiveVerifierRowsProgram[pc]? = some instruction := by
  have hpc : pc < (selectiveVerifierRowsControllerProgram 87 1744).length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveVerifierRowsControllerProgram_length] at hpc
  simp only [selectiveVerifierRowsProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowsControllerProgram_length,
      selectiveVerifierRowProgram_length]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [selectiveVerifierRowsControllerProgram_length]
    omega)]
  exact hlookup

private theorem selectiveVerifierRowsProgram_rowCallable :
    ProgramCallableAt selectiveVerifierRowsProgram selectiveVerifierRowProgram
      87 1000 50 46 := by
  intro pc instruction hlookup
  have hpc : pc < selectiveVerifierRowProgram.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [selectiveVerifierRowProgram_length] at hpc
  simp only [selectiveVerifierRowsProgram]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowsControllerProgram_length,
      selectiveVerifierRowProgram_length]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [selectiveVerifierRowsControllerProgram_length]
    omega)]
  simp only [selectiveVerifierRowsControllerProgram_length]
  rw [show 87 + pc - 87 = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem selectiveVerifierRowsProgram_emitCallable :
    ProgramCallableAt selectiveVerifierRowsProgram selectiveEmitProgram
      1744 34000 50 69 := by
  intro pc instruction hlookup
  simp only [selectiveVerifierRowsProgram]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_map,
      selectiveVerifierRowsControllerProgram_length,
      selectiveVerifierRowProgram_length]
    omega)]
  simp only [List.length_append, List.length_map,
    selectiveVerifierRowsControllerProgram_length,
    selectiveVerifierRowProgram_length]
  rw [show 1744 + pc - (87 + 1657) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

/-! ## 3. The controller's live frame -/

private theorem jump_registers_eq (machine : NPOracleState)
    (target index : ℕ) :
    (machine.jump target).registers index = machine.registers index := rfl

/-- The controller's live register frame. -/
private def VerifierRowsFrame {width bound : ℕ} (outputs : List ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (count nodeCount remaining randomnessCode spine : ℕ)
    (machine : NPOracleState) : Prop :=
  machine.registers 4 = state.target - state.next ∧
    machine.registers 6 = state.next ∧
      machine.registers 7 = selectiveSelectedCode state.selected ∧
        machine.registers 8 = encodeTaggedList outputs ∧
          machine.registers 10 = descriptionWidth width bound ∧
            machine.registers 12 = rowWidth width bound ∧
              machine.registers 14 = boundedCircuitFieldLimit width bound ∧
                machine.registers 16 = width ∧
                  machine.registers 18 = count ∧
                    machine.registers 20 = nodeCount ∧
                      machine.registers 22 = remaining ∧
                        machine.registers 26 =
                          projectionDecisionOffset width count
                            randomnessCode ∧
                          machine.registers 32 = randomnessCode ∧
                            machine.registers 34 = spine

/-! ## 4. The two constant loops

Both run before the row loop and touch only their own two registers, so each is
stated with the generic preservation clause on every other register. -/

set_option maxHeartbeats 1600000 in
-- The doubling loop: four steps per remaining exponent, then the exit test.
private theorem run_verifierRowsPowerLoop (maximumBits : ℕ) :
    ∀ (steps accumulated extraFuel finalOutput : ℕ) (machine : NPOracleState),
      natBitLength (accumulated * 2 ^ steps) ≤ maximumBits →
      natBitLength steps ≤ maximumBits →
      machine.pc = 20 →
      machine.registers 22 = accumulated →
      machine.registers 24 = steps →
      (∀ resumed : NPOracleState, resumed.pc = 24 →
        resumed.registers 22 = accumulated * 2 ^ steps →
        (∀ index : ℕ, index ≠ 22 → index ≠ 24 →
          resumed.registers index = machine.registers index) →
        runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
            resumed =
          some finalOutput) →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits
          (4 * steps + 1 + extraFuel) machine =
        some finalOutput := by
  intro steps
  induction steps with
  | zero =>
      intro accumulated extraFuel finalOutput machine _ _ hpc haccumulator
        hsteps hcontinue
      rw [show 4 * 0 + 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 20) rfl) hpc]
      rw [if_pos hsteps]
      refine hcontinue _ rfl ?_ ?_
      · rw [jump_registers_eq, haccumulator, pow_zero, Nat.mul_one]
      · intro index _ _
        rw [jump_registers_eq]
  | succ steps inductionHypothesis =>
      intro accumulated extraFuel finalOutput machine hfinalBits hstepsBits hpc
        haccumulator hsteps hcontinue
      have hdoubleBits : natBitLength (accumulated + accumulated) ≤
          maximumBits := by
        refine (natBitLength_mono ?_).trans hfinalBits
        have hpow : 1 ≤ 2 ^ steps := Nat.one_le_two_pow
        calc accumulated + accumulated = accumulated * 2 := by ring
          _ ≤ accumulated * (2 * 2 ^ steps) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = accumulated * 2 ^ (steps + 1) := by rw [pow_succ]; ring
      have hstepBits : natBitLength steps ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ steps)).trans hstepsBits
      rw [show 4 * (steps + 1) + 1 + extraFuel =
        (4 * steps + 1 + extraFuel) + 1 + 1 + 1 + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 20) rfl) hpc]
      rw [if_neg (by rw [hsteps]; omega)]
      rw [run_add_instruction (value := accumulated + accumulated)
        (selectiveVerifierRowsProgram_controllerAt (pc := 21) rfl) rfl
        (by simp [NPOracleState.jump, haccumulator]) hdoubleBits]
      rw [run_decrement_instruction (value := steps)
        (selectiveVerifierRowsProgram_controllerAt (pc := 22) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hsteps]) hstepBits]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 23) rfl) rfl]
      simp only [ite_self]
      refine inductionHypothesis (accumulated + accumulated) extraFuel
        finalOutput _ ?_ hstepBits rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump]) ?_
      · refine le_of_eq_of_le ?_ hfinalBits
        congr 1
        rw [pow_succ]
        ring
      · intro resumed hresumedPc hresumedAccumulator hresumedOther
        refine hcontinue resumed hresumedPc ?_ ?_
        · rw [hresumedAccumulator, pow_succ]
          ring
        · intro index hindexOne hindexTwo
          rw [hresumedOther index hindexOne hindexTwo]
          simp [NPOracleState.write, NPOracleState.jump, hindexOne, hindexTwo]

set_option maxHeartbeats 1600000 in
-- The cursor loop: four steps per remaining query, then the exit test.
private theorem run_verifierRowsOffsetLoop (maximumBits width : ℕ) :
    ∀ (steps accumulated extraFuel finalOutput : ℕ) (machine : NPOracleState),
      natBitLength (accumulated + steps * width) ≤ maximumBits →
      natBitLength steps ≤ maximumBits →
      machine.pc = 26 →
      machine.registers 16 = width →
      machine.registers 26 = accumulated →
      machine.registers 28 = steps →
      (∀ resumed : NPOracleState, resumed.pc = 30 →
        resumed.registers 26 = accumulated + steps * width →
        (∀ index : ℕ, index ≠ 26 → index ≠ 28 →
          resumed.registers index = machine.registers index) →
        runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
            resumed =
          some finalOutput) →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits
          (4 * steps + 1 + extraFuel) machine =
        some finalOutput := by
  intro steps
  induction steps with
  | zero =>
      intro accumulated extraFuel finalOutput machine _ _ hpc _ haccumulator
        hsteps hcontinue
      rw [show 4 * 0 + 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 26) rfl) hpc]
      rw [if_pos hsteps]
      refine hcontinue _ rfl ?_ ?_
      · rw [jump_registers_eq, haccumulator]
        simp
      · intro index _ _
        rw [jump_registers_eq]
  | succ steps inductionHypothesis =>
      intro accumulated extraFuel finalOutput machine hfinalBits hstepsBits hpc
        hwidth haccumulator hsteps hcontinue
      have hnextBits : natBitLength (accumulated + width) ≤ maximumBits := by
        refine (natBitLength_mono ?_).trans hfinalBits
        have : width ≤ (steps + 1) * width := by
          calc width = 1 * width := (Nat.one_mul width).symm
            _ ≤ (steps + 1) * width := Nat.mul_le_mul_right _ (by omega)
        omega
      have hstepBits : natBitLength steps ≤ maximumBits :=
        (natBitLength_mono (Nat.le_succ steps)).trans hstepsBits
      rw [show 4 * (steps + 1) + 1 + extraFuel =
        (4 * steps + 1 + extraFuel) + 1 + 1 + 1 + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 26) rfl) hpc]
      rw [if_neg (by rw [hsteps]; omega)]
      rw [run_add_instruction (value := accumulated + width)
        (selectiveVerifierRowsProgram_controllerAt (pc := 27) rfl) rfl
        (by simp [NPOracleState.jump, haccumulator, hwidth]) hnextBits]
      rw [run_decrement_instruction (value := steps)
        (selectiveVerifierRowsProgram_controllerAt (pc := 28) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hsteps]) hstepBits]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 29) rfl) rfl]
      simp only [ite_self]
      refine inductionHypothesis (accumulated + width) extraFuel finalOutput _
        ?_ hstepBits rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hwidth])
        (by simp [NPOracleState.write, NPOracleState.jump])
        (by simp [NPOracleState.write, NPOracleState.jump]) ?_
      · refine le_of_eq_of_le ?_ hfinalBits
        congr 1
        ring
      · intro resumed hresumedPc hresumedAccumulator hresumedOther
        refine hcontinue resumed hresumedPc ?_ ?_
        · rw [hresumedAccumulator]
          ring
        · intro index hindexOne hindexTwo
          rw [hresumedOther index hindexOne hindexTwo]
          simp [NPOracleState.write, NPOracleState.jump, hindexOne, hindexTwo]

/-! ## 5. The row loop -/

set_option maxHeartbeats 3200000 in
-- Thirteen request steps around the relocated row compiler, seven unpacking
-- steps, three spine steps and three cursor steps.
private theorem run_verifierRowsIteration {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (remaining randomnessCode : ℕ) (values : List ℕ)
    (hordered : selectiveStateOrdered state)
    (maximumBits calleeFuel extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hcalleeFuel :
      calleeFuel =
        selectiveVerifierRowRunFuel outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode)
    (hcalleeBits :
      selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount randomnessCode ≤
        maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveVerifierRowInput (selectiveStateCode state)
            (encodeTaggedList outputs) (descriptionWidth width bound)
            (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
            count nodeCount randomnessCode
            (projectionDecisionOffset width count randomnessCode)) ≤
        maximumBits)
    (hwireBits :
      natBitLength
          (Nat.pair 0
            (selectiveWireCode
              (selectiveCompileTableVerifierRow outputs width count bound state
                nodeCount hnodeCount randomnessCode))) ≤
        maximumBits)
    (hspineBits :
      natBitLength
          (selectiveCountCasesSpineCode
            ((selectiveCompileTableVerifierRow outputs width count bound state
              nodeCount hnodeCount randomnessCode).output :: values)) ≤
        maximumBits)
    (hrandomnessBits : natBitLength (randomnessCode + 1) ≤ maximumBits)
    (hcursorBits :
      natBitLength
          (projectionDecisionOffset width count (randomnessCode + 1)) ≤
        maximumBits)
    (hremainingBits : natBitLength remaining ≤ maximumBits)
    (hzeroBits : natBitLength 0 ≤ maximumBits)
    (honeBits : natBitLength 1 ≤ maximumBits)
    (hpc : machine.pc = 32)
    (hframe :
      VerifierRowsFrame outputs state count nodeCount (remaining + 1)
        randomnessCode (selectiveCountCasesSpineCode values) machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 32 →
      VerifierRowsFrame outputs
        (selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount randomnessCode).state count nodeCount remaining
        (randomnessCode + 1)
        (selectiveCountCasesSpineCode
          ((selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).output :: values)) resumed →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowsProgram maximumBits
        (1 + (13 + (calleeFuel + (7 + (7 + extraFuel))))) machine =
      some finalOutput := by
  obtain ⟨hstateRemaining, hnext, hselected, htable, harity, hrowWidth,
    hfieldLimit, hwidth, hcount, hnodeCountReg, hremaining, hcursor,
    hrandomness, hspine⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth width bound),
      selectiveStateCode candidate =
        Nat.pair (candidate.target - candidate.next)
          (Nat.pair candidate.next
            (selectiveSelectedCode candidate.selected)) := fun _ => rfl
  have hrequestForm :
      selectiveVerifierRowInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount randomnessCode
          (projectionDecisionOffset width count randomnessCode) =
        Nat.pair (selectiveStateCode state)
          (Nat.pair (encodeTaggedList outputs)
            (Nat.pair (descriptionWidth width bound)
              (Nat.pair (rowWidth width bound)
                (Nat.pair (boundedCircuitFieldLimit width bound)
                  (Nat.pair width
                    (Nat.pair count
                      (Nat.pair nodeCount
                        (Nat.pair randomnessCode
                          (projectionDecisionOffset width count
                            randomnessCode))))))))) := rfl
  have hflat := hrequestBits
  rw [hrequestForm] at hflat
  have hstateBits := natBitLength_pair_left hflat
  have hone := natBitLength_pair_right hflat
  have htwo := natBitLength_pair_right hone
  have hthree := natBitLength_pair_right htwo
  have hfour := natBitLength_pair_right hthree
  have hfive := natBitLength_pair_right hfour
  have hsix := natBitLength_pair_right hfive
  have hseven := natBitLength_pair_right hsix
  have height := natBitLength_pair_right hseven
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
  have hspineForm :
      selectiveCountCasesSpineCode
          ((selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).output :: values) =
        Nat.pair 1
          (Nat.pair
            (selectiveCompileTableVerifierRow outputs width count bound state
              nodeCount hnodeCount randomnessCode).output
            (selectiveCountCasesSpineCode values)) := rfl
  have hconsBits :
      natBitLength
          (Nat.pair
            (selectiveCompileTableVerifierRow outputs width count bound state
              nodeCount hnodeCount randomnessCode).output
            (selectiveCountCasesSpineCode values)) ≤
        maximumBits := by
    refine (natBitLength_mono ?_).trans hspineBits
    rw [hspineForm]
    exact Nat.right_le_pair 1 _
  rw [show 1 + (13 + (calleeFuel + (7 + (7 + extraFuel)))) =
    (13 + (calleeFuel + (7 + (7 + extraFuel)))) + 1 by omega]
  rw [run_branchZero_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 32) rfl) hpc]
  rw [if_neg (by rw [hremaining]; omega)]
  rw [show 13 + (calleeFuel + (7 + (7 + extraFuel))) =
    (calleeFuel + (7 + (7 + extraFuel))) + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
      1 + 1 + 1 + 1 by omega]
  rw [run_pair_instruction
    (value :=
      Nat.pair randomnessCode
        (projectionDecisionOffset width count randomnessCode))
    (selectiveVerifierRowsProgram_controllerAt (pc := 33) rfl) rfl
    (by simp [NPOracleState.jump, hrandomness, hcursor]) height]
  rw [run_pair_instruction
    (value :=
      Nat.pair nodeCount
        (Nat.pair randomnessCode
          (projectionDecisionOffset width count randomnessCode)))
    (selectiveVerifierRowsProgram_controllerAt (pc := 34) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeCountReg]) hseven]
  rw [run_pair_instruction
    (value :=
      Nat.pair count
        (Nat.pair nodeCount
          (Nat.pair randomnessCode
            (projectionDecisionOffset width count randomnessCode))))
    (selectiveVerifierRowsProgram_controllerAt (pc := 35) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hcount]) hsix]
  rw [run_pair_instruction
    (value :=
      Nat.pair width
        (Nat.pair count
          (Nat.pair nodeCount
            (Nat.pair randomnessCode
              (projectionDecisionOffset width count randomnessCode)))))
    (selectiveVerifierRowsProgram_controllerAt (pc := 36) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hwidth]) hfive]
  rw [run_pair_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound)
        (Nat.pair width
          (Nat.pair count
            (Nat.pair nodeCount
              (Nat.pair randomnessCode
                (projectionDecisionOffset width count randomnessCode))))))
    (selectiveVerifierRowsProgram_controllerAt (pc := 37) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]) hfour]
  rw [run_pair_instruction
    (value :=
      Nat.pair (rowWidth width bound)
        (Nat.pair (boundedCircuitFieldLimit width bound)
          (Nat.pair width
            (Nat.pair count
              (Nat.pair nodeCount
                (Nat.pair randomnessCode
                  (projectionDecisionOffset width count randomnessCode)))))))
    (selectiveVerifierRowsProgram_controllerAt (pc := 38) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrowWidth]) hthree]
  rw [run_pair_instruction
    (value :=
      Nat.pair (descriptionWidth width bound)
        (Nat.pair (rowWidth width bound)
          (Nat.pair (boundedCircuitFieldLimit width bound)
            (Nat.pair width
              (Nat.pair count
                (Nat.pair nodeCount
                  (Nat.pair randomnessCode
                    (projectionDecisionOffset width count
                      randomnessCode))))))))
    (selectiveVerifierRowsProgram_controllerAt (pc := 39) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, harity]) htwo]
  rw [run_pair_instruction
    (value :=
      Nat.pair (encodeTaggedList outputs)
        (Nat.pair (descriptionWidth width bound)
          (Nat.pair (rowWidth width bound)
            (Nat.pair (boundedCircuitFieldLimit width bound)
              (Nat.pair width
                (Nat.pair count
                  (Nat.pair nodeCount
                    (Nat.pair randomnessCode
                      (projectionDecisionOffset width count
                        randomnessCode)))))))))
    (selectiveVerifierRowsProgram_controllerAt (pc := 40) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, htable]) hone]
  rw [run_pair_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveVerifierRowsProgram_controllerAt (pc := 41) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnext, hselected])
    hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveVerifierRowsProgram_controllerAt (pc := 42) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateRemaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveVerifierRowInput (selectiveStateCode state)
        (encodeTaggedList outputs) (descriptionWidth width bound)
        (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
        count nodeCount randomnessCode
        (projectionDecisionOffset width count randomnessCode))
    (selectiveVerifierRowsProgram_controllerAt (pc := 43) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hrequestForm])
    hrequestBits]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 44) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 45) rfl) rfl]
  simp only [ite_self]
  rw [hcalleeFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveVerifierRowProgram)
    (calleeOutput :=
      selectiveWireCode
        (selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount randomnessCode))
    selectiveVerifierRowsProgram_rowCallable (by omega) ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro frame hframePc hframeInput
    refine run_bits_mono
      (run_selectiveVerifierRowProgram outputs count outputsRunner clausesRunner
        state nodeCount hnodeCount randomnessCode hordered frame hframePc ?_)
      hcalleeBits
    rw [hframeInput]
    simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · exact hwireBits
  · intro _rowHalt
    rw [show 7 + (7 + extraFuel) =
      (7 + extraFuel) + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_unpairRight_instruction
      (value :=
        selectiveWireCode
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode))
      (selectiveVerifierRowsProgram_controllerAt (pc := 46) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value :=
        selectiveStateCode
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).state)
      (selectiveVerifierRowsProgram_controllerAt (pc := 47) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [run_unpairRight_instruction
      (value :=
        (selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount randomnessCode).output)
      (selectiveVerifierRowsProgram_controllerAt (pc := 48) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).state.target -
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).state.next)
      (selectiveVerifierRowsProgram_controllerAt (pc := 49) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).state.next
          (selectiveSelectedCode
            (selectiveCompileTableVerifierRow outputs width count bound state
              nodeCount hnodeCount randomnessCode).state.selected))
      (selectiveVerifierRowsProgram_controllerAt (pc := 50) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [run_unpairLeft_instruction
      (value :=
        (selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount randomnessCode).state.next)
      (selectiveVerifierRowsProgram_controllerAt (pc := 51) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [run_unpairRight_instruction
      (value :=
        selectiveSelectedCode
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).state.selected)
      (selectiveVerifierRowsProgram_controllerAt (pc := 52) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    rw [show 7 + extraFuel = extraFuel + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
    rw [run_pair_instruction
      (value :=
        Nat.pair
          (selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).output
          (selectiveCountCasesSpineCode values))
      (selectiveVerifierRowsProgram_controllerAt (pc := 53) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState, hspine])
      hconsBits]
    rw [run_set_instruction
      (selectiveVerifierRowsProgram_controllerAt (pc := 54) rfl) rfl honeBits]
    rw [run_pair_instruction
      (value :=
        selectiveCountCasesSpineCode
          ((selectiveCompileTableVerifierRow outputs width count bound state
            nodeCount hnodeCount randomnessCode).output :: values))
      (selectiveVerifierRowsProgram_controllerAt (pc := 55) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hspineForm])
      hspineBits]
    rw [run_increment_instruction (value := randomnessCode + 1)
      (selectiveVerifierRowsProgram_controllerAt (pc := 56) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hrandomness])
      hrandomnessBits]
    rw [run_increment_instruction
      (value := projectionDecisionOffset width count (randomnessCode + 1))
      (selectiveVerifierRowsProgram_controllerAt (pc := 57) rfl) rfl
      (by
        simp only [NPOracleState.write, NPOracleState.jump, relocateState]
        simp only [projectionDecisionOffset] at hcursor ⊢
        simp [hcursor]
        omega)
      hcursorBits]
    rw [run_decrement_instruction (value := remaining)
      (selectiveVerifierRowsProgram_controllerAt (pc := 58) rfl) rfl
      (by
        simp [NPOracleState.write, NPOracleState.jump, relocateState,
          hremaining])
      hremainingBits]
    rw [run_branchZero_instruction
      (selectiveVerifierRowsProgram_controllerAt (pc := 59) rfl) rfl]
    simp only [ite_self]
    refine hcontinue _ rfl
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, htable,
        harity, hrowWidth, hfieldLimit, hwidth, hcount, hnodeCountReg]

/-- Interpreter fuel of the row loop from the head at `32`. -/
private def verifierRowsLoopFuel {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    SelectiveState (descriptionWidth width bound) → List ℕ → ℕ → ℕ
  | _, [], extraFuel => 1 + extraFuel
  | state, code :: rest, extraFuel =>
      1 +
        (13 +
          (selectiveVerifierRowRunFuel outputs count outputsRunner clausesRunner
              state nodeCount hnodeCount code +
            (7 +
              (7 +
                verifierRowsLoopFuel outputs count outputsRunner clausesRunner
                  nodeCount hnodeCount
                  (selectiveCompileTableVerifierRow outputs width count bound
                    state nodeCount hnodeCount code).state rest extraFuel))))

/-- Register width of the row loop from the head at `32`. -/
private def verifierRowsLoopBits {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) :
    SelectiveState (descriptionWidth width bound) → List ℕ → List ℕ → ℕ
  | _, [], _ => 0
  | state, code :: rest, values =>
      max
        (natBitLength
          (selectiveVerifierRowInput (selectiveStateCode state)
            (encodeTaggedList outputs) (descriptionWidth width bound)
            (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
            count nodeCount code
            (projectionDecisionOffset width count code))) <|
        max
          (selectiveVerifierRowRunBits outputs count outputsRunner clausesRunner
            state nodeCount hnodeCount code) <|
          max
            (natBitLength
              (Nat.pair 0
                (selectiveWireCode
                  (selectiveCompileTableVerifierRow outputs width count bound
                    state nodeCount hnodeCount code)))) <|
            max
              (natBitLength
                (selectiveCountCasesSpineCode
                  ((selectiveCompileTableVerifierRow outputs width count bound
                    state nodeCount hnodeCount code).output :: values))) <|
              max (natBitLength (code + 1)) <|
                max
                  (natBitLength
                    (projectionDecisionOffset width count (code + 1))) <|
                  max (natBitLength rest.length) <|
                    verifierRowsLoopBits outputs count outputsRunner
                      clausesRunner nodeCount hnodeCount
                      (selectiveCompileTableVerifierRow outputs width count
                        bound state nodeCount hnodeCount code).state rest
                      ((selectiveCompileTableVerifierRow outputs width count
                        bound state nodeCount hnodeCount code).output :: values)

set_option maxHeartbeats 3200000 in
-- The row loop is one induction on the randomness codes it still has to
-- compile.
private theorem run_verifierRowsLoop {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) (maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (codes : List ℕ) (randomnessCode : ℕ)
      (state : SelectiveState (descriptionWidth width bound))
      (values : List ℕ) (machine : NPOracleState)
      (extraFuel finalOutput : ℕ),
      VerifierRowsFrom randomnessCode codes →
      selectiveStateOrdered state →
      verifierRowsLoopBits outputs count outputsRunner clausesRunner nodeCount
          hnodeCount state codes values ≤
        maximumBits →
      machine.pc = 32 →
      VerifierRowsFrame outputs state count nodeCount codes.length
        randomnessCode (selectiveCountCasesSpineCode values) machine →
      (∀ resumed : NPOracleState, resumed.pc = 60 →
        VerifierRowsFrame outputs
          (verifierRowsPass outputs count nodeCount hnodeCount state codes
            values).1 count nodeCount 0 (randomnessCode + codes.length)
          (selectiveCountCasesSpineCode
            (verifierRowsPass outputs count nodeCount hnodeCount state codes
              values).2) resumed →
        runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
            resumed =
          some finalOutput) →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits
          (verifierRowsLoopFuel outputs count outputsRunner clausesRunner
            nodeCount hnodeCount state codes extraFuel) machine =
        some finalOutput := by
  intro codes
  induction codes with
  | nil =>
      intro randomnessCode state values machine extraFuel finalOutput _ _ _ hpc
        hframe hcontinue
      have hremaining := hframe.2.2.2.2.2.2.2.2.2.2.1
      simp only [verifierRowsLoopFuel]
      rw [show 1 + extraFuel = extraFuel + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 32) rfl) hpc]
      rw [if_pos (by rw [hremaining]; rfl)]
      refine hcontinue _ rfl ?_
      simp only [verifierRowsPass, List.length_nil, Nat.add_zero]
      obtain ⟨hstateRemaining, hnext, hselected, htable, harity, hrowWidth,
        hfieldLimit, hwidth, hcount, hnodeCountReg, hcountdown, hcursor,
        hrandomness, hspine⟩ := hframe
      exact ⟨hstateRemaining, hnext, hselected, htable, harity, hrowWidth,
        hfieldLimit, hwidth, hcount, hnodeCountReg, hcountdown, hcursor,
        hrandomness, hspine⟩
  | cons code rest inductionHypothesis =>
      intro randomnessCode state values machine extraFuel finalOutput hschedule
        hordered hbits hpc hframe hcontinue
      obtain ⟨hhead, hrest⟩ := hschedule
      subst hhead
      simp only [verifierRowsLoopBits] at hbits
      have hrequestBits := (Nat.le_max_left _ _).trans hbits
      have hbitsOne := (Nat.le_max_right _ _).trans hbits
      have hcalleeBits := (Nat.le_max_left _ _).trans hbitsOne
      have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
      have hwireBits := (Nat.le_max_left _ _).trans hbitsTwo
      have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
      have hspineBits := (Nat.le_max_left _ _).trans hbitsThree
      have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
      have hrandomnessBits := (Nat.le_max_left _ _).trans hbitsFour
      have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
      have hcursorBits := (Nat.le_max_left _ _).trans hbitsFive
      have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
      have hlengthBits := (Nat.le_max_left _ _).trans hbitsSix
      have hrecursiveBits := (Nat.le_max_right _ _).trans hbitsSix
      have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
        fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
      simp only [verifierRowsLoopFuel]
      refine run_verifierRowsIteration outputs count outputsRunner clausesRunner
        state nodeCount hnodeCount rest.length code values hordered maximumBits
        _ _ _ machine rfl hcalleeBits hrequestBits hwireBits hspineBits
        hrandomnessBits hcursorBits hlengthBits (hsmall 0 (by omega))
        (hsmall 1 (by omega)) hpc ?_ ?_
      · exact hframe
      intro resumed hresumedPc hresumedFrame
      have hcontinueRest :
          ∀ final : NPOracleState, final.pc = 60 →
            VerifierRowsFrame outputs
              (verifierRowsPass outputs count nodeCount hnodeCount
                (selectiveCompileTableVerifierRow outputs width count bound
                  state nodeCount hnodeCount code).state rest
                ((selectiveCompileTableVerifierRow outputs width count bound
                  state nodeCount hnodeCount code).output :: values)).1 count
              nodeCount 0 (code + 1 + rest.length)
              (selectiveCountCasesSpineCode
                (verifierRowsPass outputs count nodeCount hnodeCount
                  (selectiveCompileTableVerifierRow outputs width count bound
                    state nodeCount hnodeCount code).state rest
                  ((selectiveCompileTableVerifierRow outputs width count bound
                    state nodeCount hnodeCount code).output :: values)).2)
              final →
            runNPOracleProgram selectiveVerifierRowsProgram maximumBits
                extraFuel final =
              some finalOutput := by
        intro final hfinalPc hfinalFrame
        refine hcontinue final hfinalPc ?_
        simp only [verifierRowsPass, List.length_cons]
        rw [show code + (rest.length + 1) = code + 1 + rest.length by omega]
        exact hfinalFrame
      exact inductionHypothesis (code + 1)
        (selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount code).state
        ((selectiveCompileTableVerifierRow outputs width count bound state
          nodeCount hnodeCount code).output :: values) resumed extraFuel
        finalOutput hrest
        (selectiveCompileTableVerifierRow_ordered outputs width count bound
          state nodeCount hnodeCount code hordered)
        hrecursiveBits hresumedPc hresumedFrame hcontinueRest

/-! ## 6. The reverse `and` fold -/

-- Four steps from the exhausted row loop to the fold's constant base case.
private theorem run_verifierRowsExit {width bound : ℕ} (outputs : List ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (count nodeCount randomnessCode spine : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (machine : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hpc : machine.pc = 60)
    (hframe :
      VerifierRowsFrame outputs state count nodeCount 0 randomnessCode spine
        machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 64 →
      resumed.registers 39 =
        rawCircuitNodeCode (n := descriptionWidth width bound) (.const true) →
      VerifierRowsFrame outputs state count nodeCount 0 randomnessCode spine
        resumed →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowsProgram maximumBits (4 + extraFuel)
        machine =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  obtain ⟨hstateRemaining, hnext, hselected, htable, harity, hrowWidth,
    hfieldLimit, hwidth, hcount, hnodeCountReg, hremaining, hcursor,
    hrandomness, hspine⟩ := hframe
  have hnodeForm :
      rawCircuitNodeCode (n := descriptionWidth width bound) (.const true) =
        Nat.pair 0 1 := rfl
  rw [show 4 + extraFuel = extraFuel + 1 + 1 + 1 + 1 by omega]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 60) rfl) hpc
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 61) rfl) rfl
    (hsmall 1 (by omega))]
  rw [run_pair_instruction (value := Nat.pair 0 1)
    (selectiveVerifierRowsProgram_controllerAt (pc := 62) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hsmall (Nat.pair 0 1) (by decide))]
  rw [run_branchZero_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 63) rfl) rfl]
  simp only [ite_self]
  refine hcontinue _ rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [NPOracleState.write, NPOracleState.jump, hstateRemaining, hnext,
      hselected, htable, harity, hrowWidth, hfieldLimit, hwidth, hcount,
      hnodeCountReg, hremaining, hcursor, hrandomness, hspine]

set_option maxHeartbeats 1600000 in
-- Three request steps around the relocated append, then seven unpacking steps.
private theorem run_verifierRowsEmitCall {width bound : ℕ} (outputs : List ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (node : BooleanNode (descriptionWidth width bound))
    (count nodeCount randomnessCode spine : ℕ)
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
    (hpc : machine.pc = 64)
    (hnode : machine.registers 39 = rawCircuitNodeCode node)
    (hframe :
      VerifierRowsFrame outputs state count nodeCount 0 randomnessCode spine
        machine)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 76 →
      resumed.registers 0 = selectiveWireCode (state.emit node) →
      resumed.registers 36 = (state.emit node).output →
      VerifierRowsFrame outputs (state.emit node).state count nodeCount 0
        randomnessCode spine resumed →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowsProgram maximumBits
        (5 + (emitFuel + (7 + extraFuel))) machine =
      some finalOutput := by
  obtain ⟨hstateRemaining, hnext, hselected, htable, harity, hrowWidth,
    hfieldLimit, hwidth, hcount, hnodeCountReg, hremaining, hcursor,
    hrandomness, hspine⟩ := hframe
  have hstateForm : ∀ candidate : SelectiveState (descriptionWidth width bound),
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
    (selectiveVerifierRowsProgram_controllerAt (pc := 64) rfl) hpc
    (by rw [hnext, hselected]) hnextSelectedBits]
  rw [run_pair_instruction (value := selectiveStateCode state)
    (selectiveVerifierRowsProgram_controllerAt (pc := 65) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hstateRemaining,
        hstateForm state])
    hstateBits]
  rw [run_pair_instruction
    (value :=
      selectiveEmitInput (state.target - state.next) state.next
        (selectiveSelectedCode state.selected) (rawCircuitNodeCode node))
    (selectiveVerifierRowsProgram_controllerAt (pc := 66) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hnode, hinputForm])
    hinputBits]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 67) rfl) rfl hzeroBits]
  rw [run_branchZero_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 68) rfl) rfl]
  simp only [ite_self]
  rw [hemitFuel]
  refine run_selectiveRelocatedCall
    (source := selectiveEmitProgram)
    (calleeOutput := selectiveWireCode (state.emit node))
    selectiveVerifierRowsProgram_emitCallable (by omega) ?_ ?_ ?_ ?_ ?_
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
      (selectiveVerifierRowsProgram_controllerAt (pc := 69) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hwireFlat]
    rw [run_unpairLeft_instruction
      (value := selectiveStateCode (state.emit node).state)
      (selectiveVerifierRowsProgram_controllerAt (pc := 70) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledStateBits]
    rw [run_unpairRight_instruction (value := (state.emit node).output)
      (selectiveVerifierRowsProgram_controllerAt (pc := 71) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, selectiveWireCode])
      hcompiledOutputBits]
    rw [run_unpairLeft_instruction
      (value := (state.emit node).state.target - (state.emit node).state.next)
      (selectiveVerifierRowsProgram_controllerAt (pc := 72) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledRemainingBits]
    rw [run_unpairRight_instruction
      (value :=
        Nat.pair (state.emit node).state.next
          (selectiveSelectedCode (state.emit node).state.selected))
      (selectiveVerifierRowsProgram_controllerAt (pc := 73) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
      hcompiledTailBits]
    rw [run_unpairLeft_instruction (value := (state.emit node).state.next)
      (selectiveVerifierRowsProgram_controllerAt (pc := 74) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump]) hcompiledNextBits]
    rw [run_unpairRight_instruction
      (value := selectiveSelectedCode (state.emit node).state.selected)
      (selectiveVerifierRowsProgram_controllerAt (pc := 75) rfl) rfl
      (by simp [NPOracleState.write, NPOracleState.jump])
      hcompiledSelectedBits]
    refine hcontinue _ rfl (by simp [NPOracleState.write, NPOracleState.jump])
      (by simp [NPOracleState.write, NPOracleState.jump])
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [NPOracleState.write, NPOracleState.jump, relocateState, htable,
        harity, hrowWidth, hfieldLimit, hwidth, hcount, hnodeCountReg,
        hremaining, hcursor, hrandomness, hspine]

/-- Interpreter fuel of the reverse fold from `76`. -/
private def verifierRowsFoldFuel {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
  | _, _, [] => (0 + 1) + 1
  | state, accumulated, value :: rest =>
      10 +
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              verifierRowsFoldFuel (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest)))

/-- Register width of the reverse fold from `76`. -/
private def verifierRowsFoldBits {n : ℕ} : SelectiveState n → ℕ → List ℕ → ℕ
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
            verifierRowsFoldBits (selectiveAnd state value accumulated).state
              (selectiveAnd state value accumulated).output rest

set_option maxHeartbeats 3200000 in
-- The fold is one induction on the retained spine.
private theorem run_verifierRowsFoldLoop {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount randomnessCode maximumBits : ℕ)
    (hsevenBits : natBitLength 7 ≤ maximumBits) :
    ∀ (values : List ℕ)
      (state : SelectiveState (descriptionWidth width bound))
      (accumulated : ℕ) (machine : NPOracleState),
      selectiveStateOrdered state →
      verifierRowsFoldBits state accumulated values ≤ maximumBits →
      machine.pc = 76 →
      machine.registers 0 = Nat.pair (selectiveStateCode state) accumulated →
      machine.registers 36 = accumulated →
      VerifierRowsFrame outputs state count nodeCount 0 randomnessCode
        (selectiveCountCasesSpineCode values) machine →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits
          (verifierRowsFoldFuel state accumulated values) machine =
        some
          (selectiveWireCode
            (selectiveUnaryFold state accumulated values)) := by
  intro values
  induction values with
  | nil =>
      intro state accumulated machine _ hbits hpc hwire _ hframe
      simp only [verifierRowsFoldBits] at hbits
      simp only [verifierRowsFoldFuel]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 76) rfl) hpc]
      rw [if_pos (by rw [hframe.2.2.2.2.2.2.2.2.2.2.2.2.2]; rfl)]
      exact run_halt_instruction (fuel := 0)
        (selectiveVerifierRowsProgram_controllerAt (pc := 86) rfl) rfl
        (by rw [jump_registers_eq, hwire]; rfl) hbits
  | cons value rest inductionHypothesis =>
      intro state accumulated machine hordered hbits hpc hwire houtput hframe
      obtain ⟨hstateRemaining, hnext, hselected, htable, harity, hrowWidth,
        hfieldLimit, hwidth, hcount, hnodeCountReg, hremaining, hcursor,
        hrandomness, hspine⟩ := hframe
      simp only [verifierRowsFoldBits] at hbits
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
          rawCircuitNodeCode (n := descriptionWidth width bound)
              (.and value accumulated) =
            Nat.pair 3
              (Nat.pair (descriptionWidth width bound + value)
                (descriptionWidth width bound + accumulated)) := rfl
      have hemitForm :
          selectiveEmitInput (state.target - state.next) state.next
              (selectiveSelectedCode state.selected)
              (rawCircuitNodeCode (n := descriptionWidth width bound)
                (.and value accumulated)) =
            Nat.pair (selectiveStateCode state)
              (rawCircuitNodeCode (n := descriptionWidth width bound)
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
              (rawCircuitNodeCode (n := descriptionWidth width bound)
                (.and value accumulated)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hinputBits
        rw [hemitForm]
        exact Nat.right_le_pair _ _
      have hchildrenBits :
          natBitLength
              (Nat.pair (descriptionWidth width bound + value)
                (descriptionWidth width bound + accumulated)) ≤
            maximumBits := by
        refine (natBitLength_mono ?_).trans hcodeBits
        rw [hnodeForm]
        exact Nat.right_le_pair 3 _
      have hleftChildBits :
          natBitLength (descriptionWidth width bound + value) ≤ maximumBits :=
        (natBitLength_mono (Nat.left_le_pair _ _)).trans hchildrenBits
      have hrightChildBits :
          natBitLength (descriptionWidth width bound + accumulated) ≤
            maximumBits :=
        (natBitLength_mono (Nat.right_le_pair _ _)).trans hchildrenBits
      have hspineNonzero : machine.registers 34 ≠ 0 := by
        rw [hspine, hspineForm]
        have hone :=
          Nat.left_le_pair 1
            (Nat.pair value (selectiveCountCasesSpineCode rest))
        omega
      simp only [verifierRowsFoldFuel, selectiveUnaryFold]
      rw [show (10 : ℕ) +
          (5 +
            (selectiveEmitFuel (state.target - state.next)
                (selectiveSelectedCode state.selected) +
              (7 +
                verifierRowsFoldFuel (selectiveAnd state value accumulated).state
                  (selectiveAnd state value accumulated).output rest))) =
        (5 +
          (selectiveEmitFuel (state.target - state.next)
              (selectiveSelectedCode state.selected) +
            (7 +
              verifierRowsFoldFuel (selectiveAnd state value accumulated).state
                (selectiveAnd state value accumulated).output rest))) +
          1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by omega]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 76) rfl) hpc]
      rw [if_neg hspineNonzero]
      rw [run_unpairRight_instruction
        (value := Nat.pair value (selectiveCountCasesSpineCode rest))
        (selectiveVerifierRowsProgram_controllerAt (pc := 77) rfl) rfl
        (by rw [jump_registers_eq, hspine, hspineForm]; simp) hconsBits]
      rw [run_unpairLeft_instruction (value := value)
        (selectiveVerifierRowsProgram_controllerAt (pc := 78) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hvalueBits]
      rw [run_unpairRight_instruction
        (value := selectiveCountCasesSpineCode rest)
        (selectiveVerifierRowsProgram_controllerAt (pc := 79) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) htailSpineBits]
      rw [run_add_instruction (value := descriptionWidth width bound + value)
        (selectiveVerifierRowsProgram_controllerAt (pc := 80) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity])
        hleftChildBits]
      rw [run_add_instruction
        (value := descriptionWidth width bound + accumulated)
        (selectiveVerifierRowsProgram_controllerAt (pc := 81) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, harity, houtput])
        hrightChildBits]
      rw [run_pair_instruction
        (value :=
          Nat.pair (descriptionWidth width bound + value)
            (descriptionWidth width bound + accumulated))
        (selectiveVerifierRowsProgram_controllerAt (pc := 82) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hchildrenBits]
      rw [run_set_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 83) rfl) rfl
        (hsmall 3 (by omega))]
      rw [run_pair_instruction
        (value :=
          rawCircuitNodeCode (n := descriptionWidth width bound)
            (.and value accumulated))
        (selectiveVerifierRowsProgram_controllerAt (pc := 84) rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hnodeForm])
        hcodeBits]
      rw [run_branchZero_instruction
        (selectiveVerifierRowsProgram_controllerAt (pc := 85) rfl) rfl]
      simp only [ite_self]
      refine run_verifierRowsEmitCall outputs state (.and value accumulated)
        count nodeCount randomnessCode (selectiveCountCasesSpineCode rest)
        hordered maximumBits _ _ _ _ rfl hinputBits hwireBits
        (hsmall 0 (by omega)) rfl
        (by simp [NPOracleState.write, NPOracleState.jump])
        ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hstateRemaining]
      · simp [NPOracleState.write, NPOracleState.jump, hnext]
      · simp [NPOracleState.write, NPOracleState.jump, hselected]
      · simp [NPOracleState.write, NPOracleState.jump, htable]
      · simp [NPOracleState.write, NPOracleState.jump, harity]
      · simp [NPOracleState.write, NPOracleState.jump, hrowWidth]
      · simp [NPOracleState.write, NPOracleState.jump, hfieldLimit]
      · simp [NPOracleState.write, NPOracleState.jump, hwidth]
      · simp [NPOracleState.write, NPOracleState.jump, hcount]
      · simp [NPOracleState.write, NPOracleState.jump, hnodeCountReg]
      · simp [NPOracleState.write, NPOracleState.jump, hremaining]
      · simp [NPOracleState.write, NPOracleState.jump, hcursor]
      · simp [NPOracleState.write, NPOracleState.jump, hrandomness]
      · simp [NPOracleState.write, NPOracleState.jump]
      · intro resumed hresumedPc hresumedWire hresumedOutput hresumedFrame
        exact inductionHypothesis (selectiveAnd state value accumulated).state
          (selectiveAnd state value accumulated).output resumed
          (selectiveState_emit_ordered state (.and value accumulated) hordered)
          hrecursiveBits hresumedPc hresumedWire hresumedOutput hresumedFrame

/-! ## 7. The request parser and the level runner -/

set_option maxHeartbeats 1600000 in
-- Eighteen parser steps and the four constant-loop set-up steps.
private theorem run_verifierRowsPrologue {width bound : ℕ} (outputs : List ℕ)
    (state : SelectiveState (descriptionWidth width bound))
    (count nodeCount : ℕ)
    (maximumBits extraFuel finalOutput : ℕ) (entry : NPOracleState)
    (hsevenBits : natBitLength 7 ≤ maximumBits)
    (hrequestBits :
      natBitLength
          (selectiveVerifierRowsInput (selectiveStateCode state)
            (encodeTaggedList outputs) (descriptionWidth width bound)
            (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
            count nodeCount) ≤
        maximumBits)
    (hrowsBits : natBitLength (2 ^ width) ≤ maximumBits)
    (hcursorBits : natBitLength (count * width) ≤ maximumBits)
    (hpc : entry.pc = 0)
    (hinput :
      entry.registers 0 =
        selectiveVerifierRowsInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount)
    (hcontinue : ∀ resumed : NPOracleState, resumed.pc = 32 →
      VerifierRowsFrame outputs state count nodeCount (2 ^ width) 0
        (selectiveCountCasesSpineCode []) resumed →
      runNPOracleProgram selectiveVerifierRowsProgram maximumBits extraFuel
          resumed =
        some finalOutput) :
    runNPOracleProgram selectiveVerifierRowsProgram maximumBits
        (18 + (2 + ((4 * width + 1) + (2 + ((4 * count + 1) + (2 + extraFuel))))))
        entry =
      some finalOutput := by
  have hsmall : ∀ value : ℕ, value ≤ 7 → natBitLength value ≤ maximumBits :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hstateForm :
      selectiveStateCode state =
        Nat.pair (state.target - state.next)
          (Nat.pair state.next (selectiveSelectedCode state.selected)) := rfl
  have hflat := hrequestBits
  simp only [selectiveVerifierRowsInput] at hflat
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
  have hnodeCountBits := natBitLength_pair_right hsix
  have hstateFlat := hstateBits
  rw [hstateForm] at hstateFlat
  have hremainingBits := natBitLength_pair_left hstateFlat
  have htailState := natBitLength_pair_right hstateFlat
  have hnextBits := natBitLength_pair_left htailState
  have hselectedBits := natBitLength_pair_right htailState
  rw [show (18 : ℕ) +
      (2 + ((4 * width + 1) + (2 + ((4 * count + 1) + (2 + extraFuel))))) =
    (2 + ((4 * width + 1) + (2 + ((4 * count + 1) + (2 + extraFuel))))) +
      1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by
    omega]
  rw [run_unpairLeft_instruction (value := selectiveStateCode state)
    (selectiveVerifierRowsProgram_controllerAt (pc := 0) rfl) hpc
    (by rw [hinput]; simp [selectiveVerifierRowsInput]) hstateBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (encodeTaggedList outputs) <|
        Nat.pair (descriptionWidth width bound) <|
          Nat.pair (rowWidth width bound) <|
            Nat.pair (boundedCircuitFieldLimit width bound) <|
              Nat.pair width (Nat.pair count nodeCount))
    (selectiveVerifierRowsProgram_controllerAt (pc := 1) rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hinput,
        selectiveVerifierRowsInput])
    hone]
  rw [run_unpairLeft_instruction (value := state.target - state.next)
    (selectiveVerifierRowsProgram_controllerAt (pc := 2) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm])
    hremainingBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair state.next (selectiveSelectedCode state.selected))
    (selectiveVerifierRowsProgram_controllerAt (pc := 3) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hstateForm]) htailState]
  rw [run_unpairLeft_instruction (value := state.next)
    (selectiveVerifierRowsProgram_controllerAt (pc := 4) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnextBits]
  rw [run_unpairRight_instruction
    (value := selectiveSelectedCode state.selected)
    (selectiveVerifierRowsProgram_controllerAt (pc := 5) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hselectedBits]
  rw [run_unpairLeft_instruction (value := encodeTaggedList outputs)
    (selectiveVerifierRowsProgram_controllerAt (pc := 6) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htableBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (descriptionWidth width bound) <|
        Nat.pair (rowWidth width bound) <|
          Nat.pair (boundedCircuitFieldLimit width bound) <|
            Nat.pair width (Nat.pair count nodeCount))
    (selectiveVerifierRowsProgram_controllerAt (pc := 7) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) htwo]
  rw [run_unpairLeft_instruction (value := descriptionWidth width bound)
    (selectiveVerifierRowsProgram_controllerAt (pc := 8) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) harityBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (rowWidth width bound) <|
        Nat.pair (boundedCircuitFieldLimit width bound) <|
          Nat.pair width (Nat.pair count nodeCount))
    (selectiveVerifierRowsProgram_controllerAt (pc := 9) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hthree]
  rw [run_unpairLeft_instruction (value := rowWidth width bound)
    (selectiveVerifierRowsProgram_controllerAt (pc := 10) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hrowWidthBits]
  rw [run_unpairRight_instruction
    (value :=
      Nat.pair (boundedCircuitFieldLimit width bound) <|
        Nat.pair width (Nat.pair count nodeCount))
    (selectiveVerifierRowsProgram_controllerAt (pc := 11) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfour]
  rw [run_unpairLeft_instruction
    (value := boundedCircuitFieldLimit width bound)
    (selectiveVerifierRowsProgram_controllerAt (pc := 12) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfieldLimitBits]
  rw [run_unpairRight_instruction
    (value := Nat.pair width (Nat.pair count nodeCount))
    (selectiveVerifierRowsProgram_controllerAt (pc := 13) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hfive]
  rw [run_unpairLeft_instruction (value := width)
    (selectiveVerifierRowsProgram_controllerAt (pc := 14) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  rw [run_unpairRight_instruction (value := Nat.pair count nodeCount)
    (selectiveVerifierRowsProgram_controllerAt (pc := 15) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsix]
  rw [run_unpairLeft_instruction (value := count)
    (selectiveVerifierRowsProgram_controllerAt (pc := 16) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hcountBits]
  rw [run_unpairRight_instruction (value := nodeCount)
    (selectiveVerifierRowsProgram_controllerAt (pc := 17) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hnodeCountBits]
  rw [show (2 : ℕ) + ((4 * width + 1) + (2 + ((4 * count + 1) + (2 + extraFuel)))) =
    ((4 * width + 1) + (2 + ((4 * count + 1) + (2 + extraFuel)))) + 1 + 1 by
    omega]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 18) rfl) rfl
    (hsmall 1 (by omega))]
  rw [run_copy_instruction (value := width)
    (selectiveVerifierRowsProgram_controllerAt (pc := 19) rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hwidthBits]
  refine run_verifierRowsPowerLoop maximumBits width 1 _ _ _
    (by simpa using hrowsBits) hwidthBits rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro afterPower hpowerPc hpowerRows hpowerOther
  rw [show (2 : ℕ) + ((4 * count + 1) + (2 + extraFuel)) =
    ((4 * count + 1) + (2 + extraFuel)) + 1 + 1 by omega]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 24) rfl) hpowerPc
    (hsmall 0 (by omega))]
  rw [run_copy_instruction (value := count)
    (selectiveVerifierRowsProgram_controllerAt (pc := 25) rfl) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump]
      rw [show (18 : ℕ) = 18 from rfl]
      simp [hpowerOther 18 (by omega) (by omega)])
    hcountBits]
  refine run_verifierRowsOffsetLoop maximumBits width count 0 _ _ _
    (by simpa using hcursorBits) hcountBits rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump]
      simp [hpowerOther 16 (by omega) (by omega)])
    (by simp [NPOracleState.write, NPOracleState.jump])
    (by simp [NPOracleState.write, NPOracleState.jump]) ?_
  intro afterOffset hoffsetPc hoffsetCursor hoffsetOther
  rw [show (2 : ℕ) + extraFuel = extraFuel + 1 + 1 by omega]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 30) rfl) hoffsetPc
    (hsmall 0 (by omega))]
  rw [run_set_instruction
    (selectiveVerifierRowsProgram_controllerAt (pc := 31) rfl) rfl
    (hsmall 0 (by omega))]
  refine hcontinue _ rfl
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 4 (by omega) (by omega),
      hpowerOther 4 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 6 (by omega) (by omega),
      hpowerOther 6 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 7 (by omega) (by omega),
      hpowerOther 7 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 8 (by omega) (by omega),
      hpowerOther 8 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 10 (by omega) (by omega),
      hpowerOther 10 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 12 (by omega) (by omega),
      hpowerOther 12 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 14 (by omega) (by omega),
      hpowerOther 14 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 16 (by omega) (by omega),
      hpowerOther 16 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 18 (by omega) (by omega),
      hpowerOther 18 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 20 (by omega) (by omega),
      hpowerOther 20 (by omega) (by omega)]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetOther 22 (by omega) (by omega), hpowerRows]
  · simp only [NPOracleState.write, NPOracleState.jump]
    simp [hoffsetCursor, projectionDecisionOffset]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump, selectiveCountCasesSpineCode]

/-- The compiler state and retained spine after every verifier row. -/
private def verifierRowsAfter {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound)) :
    SelectiveState (descriptionWidth width bound) × List ℕ :=
  verifierRowsPass outputs count nodeCount hnodeCount state
    (List.range (2 ^ width)) []

/-- The fold's constant base case. -/
private def verifierRowsBaseWire {width bound : ℕ} (outputs : List ℕ)
    (count nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (state : SelectiveState (descriptionWidth width bound)) :
    SelectiveWire (descriptionWidth width bound) :=
  selectiveConst
    (verifierRowsAfter outputs count nodeCount hnodeCount state).1 true

/-- Interpreter fuel of one whole verifier-row schedule. -/
def selectiveVerifierRowsRunFuel {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) : ℕ :=
  18 +
    (2 +
      ((4 * width + 1) +
        (2 +
          ((4 * count + 1) +
            (2 +
              verifierRowsLoopFuel outputs count outputsRunner clausesRunner
                nodeCount hnodeCount state (List.range (2 ^ width))
                (4 +
                  (5 +
                    (selectiveEmitFuel
                        ((verifierRowsAfter outputs count nodeCount hnodeCount
                            state).1.target -
                          (verifierRowsAfter outputs count nodeCount hnodeCount
                            state).1.next)
                        (selectiveSelectedCode
                          (verifierRowsAfter outputs count nodeCount hnodeCount
                            state).1.selected) +
                      (7 +
                        verifierRowsFoldFuel
                          (verifierRowsBaseWire outputs count nodeCount
                            hnodeCount state).state
                          (verifierRowsBaseWire outputs count nodeCount
                            hnodeCount state).output
                          (verifierRowsAfter outputs count nodeCount hnodeCount
                            state).2)))))))))

/-- Register width of one whole verifier-row schedule. -/
def selectiveVerifierRowsRunBits {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound) : ℕ :=
  max (natBitLength 7) <|
    max
      (natBitLength
        (selectiveVerifierRowsInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount)) <|
      max (natBitLength (2 ^ width)) <|
        max (natBitLength (count * width)) <|
          max
            (verifierRowsLoopBits outputs count outputsRunner clausesRunner
              nodeCount hnodeCount state (List.range (2 ^ width)) []) <|
            max
              (natBitLength
                (selectiveEmitInput
                  ((verifierRowsAfter outputs count nodeCount hnodeCount
                      state).1.target -
                    (verifierRowsAfter outputs count nodeCount hnodeCount
                      state).1.next)
                  (verifierRowsAfter outputs count nodeCount hnodeCount
                    state).1.next
                  (selectiveSelectedCode
                    (verifierRowsAfter outputs count nodeCount hnodeCount
                      state).1.selected)
                  (rawCircuitNodeCode (n := descriptionWidth width bound)
                    (.const true)))) <|
              max
                (natBitLength
                  (Nat.pair 0
                    (selectiveWireCode
                      (verifierRowsBaseWire outputs count nodeCount hnodeCount
                        state)))) <|
                verifierRowsFoldBits
                  (verifierRowsBaseWire outputs count nodeCount hnodeCount
                    state).state
                  (verifierRowsBaseWire outputs count nodeCount hnodeCount
                    state).output
                  (verifierRowsAfter outputs count nodeCount hnodeCount state).2

set_option maxHeartbeats 1600000 in
-- The parser, the two constant loops, the row loop and the reverse fold.
/-- **The verifier-row scheduler's run.**  The `1762`-instruction stream started
on its own ABI frame, at any entry registers, returns exactly the compiler wire
the source compiler produces for all `2 ^ width` verifier rows of one candidate
node count. -/
theorem run_selectiveVerifierRowsProgram {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count)
    (state : SelectiveState (descriptionWidth width bound))
    (nodeCount : ℕ) (hnodeCount : nodeCount ≤ bound)
    (hordered : selectiveStateOrdered state)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        selectiveVerifierRowsInput (selectiveStateCode state)
          (encodeTaggedList outputs) (descriptionWidth width bound)
          (rowWidth width bound) (boundedCircuitFieldLimit width bound) width
          count nodeCount) :
    runNPOracleProgram selectiveVerifierRowsProgram
        (selectiveVerifierRowsRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount)
        (selectiveVerifierRowsRunFuel outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount) entry =
      some
        (selectiveWireCode
          (selectiveCompileTableVerifierRows outputs width count bound nodeCount
            hnodeCount state (List.range (2 ^ width)))) := by
  have hbits :
      selectiveVerifierRowsRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount ≤
        selectiveVerifierRowsRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount := le_refl _
  unfold selectiveVerifierRowsRunBits at hbits
  have hsevenBits := (Nat.le_max_left _ _).trans hbits
  have hbitsOne := (Nat.le_max_right _ _).trans hbits
  have hrequestBits := (Nat.le_max_left _ _).trans hbitsOne
  have hbitsTwo := (Nat.le_max_right _ _).trans hbitsOne
  have hrowsBits := (Nat.le_max_left _ _).trans hbitsTwo
  have hbitsThree := (Nat.le_max_right _ _).trans hbitsTwo
  have hcursorBits := (Nat.le_max_left _ _).trans hbitsThree
  have hbitsFour := (Nat.le_max_right _ _).trans hbitsThree
  have hloopBits := (Nat.le_max_left _ _).trans hbitsFour
  have hbitsFive := (Nat.le_max_right _ _).trans hbitsFour
  have hemitInputBits := (Nat.le_max_left _ _).trans hbitsFive
  have hbitsSix := (Nat.le_max_right _ _).trans hbitsFive
  have hemitWireBits := (Nat.le_max_left _ _).trans hbitsSix
  have hfoldBits := (Nat.le_max_right _ _).trans hbitsSix
  have hsmall : ∀ value : ℕ, value ≤ 7 →
      natBitLength value ≤
        selectiveVerifierRowsRunBits outputs count outputsRunner clausesRunner
          state nodeCount hnodeCount :=
    fun value hvalue => (natBitLength_mono hvalue).trans hsevenBits
  have hpass :
      verifierRowsAfter outputs count nodeCount hnodeCount state =
        ((verifierRowsHeads outputs count nodeCount hnodeCount state
            (List.range (2 ^ width))).state,
          (verifierRowsHeads outputs count nodeCount hnodeCount state
            (List.range (2 ^ width))).values.reverse) := by
    rw [verifierRowsAfter, verifierRowsPass_eq]
    simp
  have hfold :
      selectiveCompileTableVerifierRows outputs width count bound nodeCount
          hnodeCount state (List.range (2 ^ width)) =
        selectiveUnaryFold
          (verifierRowsBaseWire outputs count nodeCount hnodeCount state).state
          (verifierRowsBaseWire outputs count nodeCount hnodeCount state).output
          (verifierRowsAfter outputs count nodeCount hnodeCount state).2 := by
    rw [selectiveCompileTableVerifierRows_eq_fold, verifierRowsBaseWire, hpass]
  have horderedAfter :
      selectiveStateOrdered
        (verifierRowsAfter outputs count nodeCount hnodeCount state).1 := by
    rw [hpass]
    exact verifierRowsHeads_ordered outputs count nodeCount hnodeCount _ state
      hordered
  rw [hfold]
  unfold selectiveVerifierRowsRunFuel
  refine run_verifierRowsPrologue outputs state count nodeCount _ _ _ entry
    hsevenBits hrequestBits hrowsBits hcursorBits hentryPc hentryInput ?_
  intro afterPrologue hprologuePc hprologueFrame
  refine run_verifierRowsLoop outputs count outputsRunner clausesRunner
    nodeCount hnodeCount _ hsevenBits (List.range (2 ^ width)) 0 state []
    afterPrologue _ _ (verifierRowsFrom_range (2 ^ width)) hordered hloopBits
    hprologuePc ?_ ?_
  · rw [List.length_range]
    exact hprologueFrame
  intro afterRows hrowsPc hrowsFrame
  refine run_verifierRowsExit outputs
    (verifierRowsAfter outputs count nodeCount hnodeCount state).1 count
    nodeCount (0 + (List.range (2 ^ width)).length) _ _ _ _ afterRows
    hsevenBits hrowsPc hrowsFrame ?_
  intro afterBase hbasePc hbaseNode hbaseFrame
  refine run_verifierRowsEmitCall outputs
    (verifierRowsAfter outputs count nodeCount hnodeCount state).1 (.const true)
    count nodeCount _ _ horderedAfter _ _ _ _ afterBase rfl hemitInputBits
    hemitWireBits (hsmall 0 (by omega)) hbasePc hbaseNode hbaseFrame ?_
  intro afterEmit hemitPc hemitWire hemitOutput hemitFrame
  exact run_verifierRowsFoldLoop outputs count nodeCount _ _ hsevenBits
    (verifierRowsAfter outputs count nodeCount hnodeCount state).2
    (verifierRowsBaseWire outputs count nodeCount hnodeCount state).state
    (verifierRowsBaseWire outputs count nodeCount hnodeCount state).output
    afterEmit (selectiveState_emit_ordered _ _ horderedAfter) hfoldBits hemitPc
    hemitWire hemitOutput hemitFrame

/-- **The verifier-row level, from the levels below it.**  The projected query
compiler's run and the clause-list compiler's run build the verifier-row runner
the fixed-count controller one level up consumes. -/
def selectiveVerifierRowsRunnerOfLevels {width bound : ℕ} (outputs : List ℕ)
    (count : ℕ)
    (outputsRunner : SelectiveUniversalOutputsRunner outputs width bound)
    (clausesRunner :
      SelectiveClausesRunner (descriptionWidth width bound) count) :
    SelectiveVerifierRowsRunner outputs width count bound where
  bits state nodeCount :=
    if hnodeCount : nodeCount ≤ bound then
      selectiveVerifierRowsRunBits outputs count outputsRunner clausesRunner
        state nodeCount hnodeCount
    else 0
  fuel state nodeCount :=
    if hnodeCount : nodeCount ≤ bound then
      selectiveVerifierRowsRunFuel outputs count outputsRunner clausesRunner
        state nodeCount hnodeCount
    else 0
  executes := by
    intro state nodeCount hnodeCount hordered entry hentryPc hentryInput
    rw [dif_pos hnodeCount, dif_pos hnodeCount]
    exact run_selectiveVerifierRowsProgram outputs count outputsRunner
      clausesRunner state nodeCount hnodeCount hordered entry hentryPc
      hentryInput

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
