import Proof.Foundations.CanonicalBinaryProgram
import Proof.Foundations.PolynomialClock
import Proof.Foundations.VerifiedLinker

/-!
# Fixed tagged program choice

`taggedProgramChoice first second` consumes `pair(tag, payload)`, runs `first`
when `tag = 0`, and runs `second` otherwise.  Both branches share one isolated
handoff register and one return halt, so callers do not need parallel wrapper
implementations for heterogeneous balanced calls.
-/

namespace NearCubicWires.TaggedProgramChoice

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

private def choiceTransferRegister
    (first second : NPOracleProgram) : ℕ :=
  max (programRegisterSpan first) (programRegisterSpan second)

private def choiceFirstBase : ℕ := 5

private def choiceSecondBase (first : NPOracleProgram) : ℕ :=
  choiceFirstBase + first.length

private def choiceReturnPc
    (first second : NPOracleProgram) : ℕ :=
  choiceSecondBase first + second.length

/-- One fixed tag dispatcher.  The source programs execute unchanged except
for verified control-flow continuation at their halt instructions. -/
def taggedProgramChoice
    (first second : NPOracleProgram) : NPOracleProgram :=
  ((([.unpairLeft 0 2 1,
       .unpairRight 0 0 2,
       .branchZero 2 3 4,
       .set 2 0 choiceFirstBase,
       .set 2 0 (choiceSecondBase first)] ++
      first.map
        (continueInstruction choiceFirstBase
          (choiceTransferRegister first second)
          (choiceReturnPc first second))) ++
    second.map
      (continueInstruction (choiceSecondBase first)
        (choiceTransferRegister first second)
        (choiceReturnPc first second))) ++
  [.halt (choiceTransferRegister first second)])

def taggedProgramChoiceFuel (sourceFuel : ℕ) : ℕ :=
  sourceFuel + 5

private def firstChoiceLayout
    (first second : NPOracleProgram) : LinkLayout where
  firstSpan := programRegisterSpan first
  secondSpan := 0
  firstBase := choiceFirstBase
  resetBase := choiceReturnPc first second
  secondBase := choiceReturnPc first second
  secondRegisterBase := choiceTransferRegister first second + 1
  savedLengthRegister := choiceTransferRegister first second + 1
  transferRegister := choiceTransferRegister first second

private def secondChoiceLayout
    (first second : NPOracleProgram) : LinkLayout where
  firstSpan := programRegisterSpan second
  secondSpan := 0
  firstBase := choiceSecondBase first
  resetBase := choiceReturnPc first second
  secondBase := choiceReturnPc first second
  secondRegisterBase := choiceTransferRegister first second + 1
  savedLengthRegister := choiceTransferRegister first second + 1
  transferRegister := choiceTransferRegister first second

private theorem firstChoiceContinued
    (first second : NPOracleProgram) :
    ProgramContinuedAt (taggedProgramChoice first second) first
      choiceFirstBase (choiceTransferRegister first second)
      (choiceReturnPc first second) := by
  intro pc instruction hlookup
  have hpc : pc < first.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [taggedProgramChoice, choiceFirstBase, choiceSecondBase,
    choiceReturnPc]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  simp only [List.length_cons, List.length_nil]
  rw [show 5 + pc - (0 + 1 + 1 + 1 + 1 + 1) = pc by omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem secondChoiceContinued
    (first second : NPOracleProgram) :
    ProgramContinuedAt (taggedProgramChoice first second) second
      (choiceSecondBase first) (choiceTransferRegister first second)
      (choiceReturnPc first second) := by
  intro pc instruction hlookup
  have hpc : pc < second.length :=
    (List.getElem?_eq_some_iff.mp hlookup).choose
  simp only [taggedProgramChoice, choiceFirstBase, choiceSecondBase,
    choiceReturnPc]
  rw [List.getElem?_append_left (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  rw [show
      5 + first.length + pc -
          (0 + 1 + 1 + 1 + 1 + 1 + first.length) = pc by
    omega]
  rw [List.getElem?_map, hlookup]
  rfl

private theorem choiceState_ext (left right : NPOracleState)
    (hpc : left.pc = right.pc)
    (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem choiceEntryState
    (layout : LinkLayout) (inputLength payload : ℕ)
    (hspan : 2 ≤ layout.firstSpan) :
    let source := initialNPOracleState inputLength payload
    source.jump layout.firstBase =
      firstStageState layout 0 source := by
  dsimp only
  apply choiceState_ext
  · rfl
  · funext register
    by_cases hlow : register < layout.firstSpan
    · simp [firstStageState, hlow]
    · have hregister : 2 ≤ register := by omega
      have hzero : register ≠ 0 := by omega
      have hone : register ≠ 1 := by omega
      simp [firstStageState, hlow, initialNPOracleState, hzero, hone]

private theorem choiceReturn
    (first second : NPOracleProgram) :
    (taggedProgramChoice first second)[choiceReturnPc first second]? =
      some (.halt (choiceTransferRegister first second)) := by
  simp only [taggedProgramChoice, choiceReturnPc, choiceSecondBase,
    choiceFirstBase]
  rw [List.getElem?_append_right (by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map]
    omega)]
  simp only [List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  rw [show
      5 + first.length + second.length -
        (5 + first.length + second.length) = 0 by omega]
  rfl

private theorem taggedPayload_bits
    {inputLength tag payload maximumBits : ℕ}
    (hbits :
      natBitLength (Nat.pair inputLength (Nat.pair tag payload)) ≤
        maximumBits) :
    natBitLength payload ≤ maximumBits := by
  apply (natBitLength_mono ?_).trans hbits
  exact (Nat.right_le_pair tag payload).trans
    (Nat.right_le_pair inputLength (Nat.pair tag payload))

private theorem taggedTag_bits
    {inputLength tag payload maximumBits : ℕ}
    (hbits :
      natBitLength (Nat.pair inputLength (Nat.pair tag payload)) ≤
        maximumBits) :
    natBitLength tag ≤ maximumBits := by
  apply (natBitLength_mono ?_).trans hbits
  exact (Nat.left_le_pair tag payload).trans
    (Nat.right_le_pair inputLength (Nat.pair tag payload))

private theorem choiceDispatchState
    (inputLength tag payload base : ℕ) :
    let initial :=
      initialNPOracleState inputLength (Nat.pair tag payload)
    let state1 := (initial.write 2 tag).jump 1
    let state2 := (state1.write 0 payload).jump 2
    let state3 :=
      state2.jump (if state2.registers 2 = 0 then 3 else 4)
    ((state3.write 2 0).jump base) =
      (initialNPOracleState inputLength payload).jump base := by
  dsimp only
  apply choiceState_ext
  · rfl
  · funext register
    by_cases hzero : register = 0
    · subst register
      simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
    · by_cases hone : register = 1
      · subst register
        simp [initialNPOracleState, NPOracleState.write,
          NPOracleState.jump]
      · by_cases htwo : register = 2
        · subst register
          simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump]
        · simp [initialNPOracleState, NPOracleState.write,
            NPOracleState.jump, hzero, hone, htwo]

theorem taggedProgramChoice_oracleFree
    (first second : NPOracleProgram)
    (hfirst : OracleFree first) (hsecond : OracleFree second) :
    OracleFree (taggedProgramChoice first second) := by
  rw [oracleFree_iff_containsSAT_false]
  have hfirstContains :=
    (oracleFree_iff_containsSAT_false first).mp hfirst
  have hsecondContains :=
    (oracleFree_iff_containsSAT_false second).mp hsecond
  calc
    containsSAT (taggedProgramChoice first second) =
        (containsSAT first || containsSAT second) := by
      simp only [containsSAT, taggedProgramChoice, List.cons_append,
        List.nil_append, List.any_cons, List.any_append, List.any_map,
        Function.comp_def, containsSAT_continueInstruction, List.any_nil,
        Bool.or_self, Bool.or_false, Bool.false_or]
    _ = false :=
      Bool.or_eq_false_iff.mpr ⟨hfirstContains, hsecondContains⟩

/-- Exact zero-tag branch. -/
theorem run_taggedProgramChoice_zero
    (first second : NPOracleProgram)
    (inputLength payload maximumBits sourceFuel output : ℕ)
    (hinput :
      natBitLength
          (Nat.pair inputLength (Nat.pair 0 payload)) ≤ maximumBits)
    (hsource :
      runNPOracleProgram first maximumBits sourceFuel
          (initialNPOracleState inputLength payload) =
        some output)
    (houtput : natBitLength output ≤ maximumBits) :
    runNPOracleProgram (taggedProgramChoice first second) maximumBits
        (taggedProgramChoiceFuel sourceFuel)
        (initialNPOracleState inputLength (Nat.pair 0 payload)) =
      some output := by
  have hzero : natBitLength 0 ≤ maximumBits :=
    taggedTag_bits hinput
  have hpayload : natBitLength payload ≤ maximumBits :=
    taggedPayload_bits hinput
  rw [show taggedProgramChoiceFuel sourceFuel =
      (sourceFuel + 4) + 1 by
    simp only [taggedProgramChoiceFuel]]
  rw [run_unpairLeft_instruction
    (program := taggedProgramChoice first second)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := 0) (by rfl) rfl
    (by simp [initialNPOracleState]) hzero]
  rw [show sourceFuel + 4 = (sourceFuel + 3) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := taggedProgramChoice first second)
    (pc := 1) (source := 0) (destination := 0) (next := 2)
    (value := payload) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hpayload]
  rw [show sourceFuel + 3 = (sourceFuel + 2) + 1 by omega]
  rw [run_branchZero_instruction
    (program := taggedProgramChoice first second)
    (pc := 2) (register := 2) (zeroTarget := 3)
    (nonzeroTarget := 4) (by rfl) rfl]
  rw [show sourceFuel + 2 = (sourceFuel + 1) + 1 by omega]
  rw [run_set_instruction
    (program := taggedProgramChoice first second)
    (pc := 3) (register := 2) (value := 0)
    (next := choiceFirstBase) (by rfl) rfl hzero]
  rw [choiceDispatchState inputLength 0 payload choiceFirstBase]
  let source := initialNPOracleState inputLength payload
  have hentry :
      source.jump (firstChoiceLayout first second).firstBase =
        firstStageState (firstChoiceLayout first second) 0 source := by
    exact choiceEntryState (firstChoiceLayout first second)
      inputLength payload (by
        simpa only [firstChoiceLayout] using
          (two_le_programRegisterSpan first))
  change
    runNPOracleProgram (taggedProgramChoice first second) maximumBits
        (sourceFuel + 1) (source.jump choiceFirstBase) =
      some output
  rw [show choiceFirstBase =
      (firstChoiceLayout first second).firstBase by rfl, hentry]
  apply run_continued
    (layout := firstChoiceLayout first second)
    (by
      simpa only [firstChoiceLayout] using
        (firstChoiceContinued first second))
    (le_refl (programRegisterSpan first))
    hsource
  intro haltState unused
  apply run_halt_instruction (choiceReturn first second)
  · rfl
  · simp [firstChoiceLayout, NPOracleState.write, NPOracleState.jump]
  · exact houtput

/-- Exact nonzero-tag branch.  All nonzero tags deliberately select the same
second program, matching the machine's total `branchZero` semantics. -/
theorem run_taggedProgramChoice_nonzero
    (first second : NPOracleProgram)
    (inputLength tag payload maximumBits sourceFuel output : ℕ)
    (htag : tag ≠ 0)
    (hinput :
      natBitLength
          (Nat.pair inputLength (Nat.pair tag payload)) ≤ maximumBits)
    (hsource :
      runNPOracleProgram second maximumBits sourceFuel
          (initialNPOracleState inputLength payload) =
        some output)
    (houtput : natBitLength output ≤ maximumBits) :
    runNPOracleProgram (taggedProgramChoice first second) maximumBits
        (taggedProgramChoiceFuel sourceFuel)
        (initialNPOracleState inputLength (Nat.pair tag payload)) =
      some output := by
  have htagBits : natBitLength tag ≤ maximumBits :=
    taggedTag_bits hinput
  have hpayload : natBitLength payload ≤ maximumBits :=
    taggedPayload_bits hinput
  have hzero : natBitLength 0 ≤ maximumBits := by
    exact (natBitLength_mono (Nat.zero_le tag)).trans htagBits
  rw [show taggedProgramChoiceFuel sourceFuel =
      (sourceFuel + 4) + 1 by
    simp only [taggedProgramChoiceFuel]]
  rw [run_unpairLeft_instruction
    (program := taggedProgramChoice first second)
    (pc := 0) (source := 0) (destination := 2) (next := 1)
    (value := tag) (by rfl) rfl
    (by simp [initialNPOracleState]) htagBits]
  rw [show sourceFuel + 4 = (sourceFuel + 3) + 1 by omega]
  rw [run_unpairRight_instruction
    (program := taggedProgramChoice first second)
    (pc := 1) (source := 0) (destination := 0) (next := 2)
    (value := payload) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump]) hpayload]
  rw [show sourceFuel + 3 = (sourceFuel + 2) + 1 by omega]
  rw [run_branchZero_instruction
    (program := taggedProgramChoice first second)
    (pc := 2) (register := 2) (zeroTarget := 3)
    (nonzeroTarget := 4) (by rfl) rfl]
  rw [if_neg (by
    simpa [initialNPOracleState, NPOracleState.write,
      NPOracleState.jump] using htag)]
  rw [show sourceFuel + 2 = (sourceFuel + 1) + 1 by omega]
  rw [run_set_instruction
    (program := taggedProgramChoice first second)
    (pc := 4) (register := 2) (value := 0)
    (next := choiceSecondBase first) (by rfl) rfl hzero]
  have hdispatch :=
    choiceDispatchState inputLength tag payload (choiceSecondBase first)
  dsimp only at hdispatch
  rw [show
      (((((initialNPOracleState inputLength
        (Nat.pair tag payload)).write 2 tag).jump 1).write 0 payload).jump
          2).registers 2 = tag by
    simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]]
    at hdispatch
  rw [if_neg htag] at hdispatch
  rw [hdispatch]
  let source := initialNPOracleState inputLength payload
  have hentry :
      source.jump (secondChoiceLayout first second).firstBase =
        firstStageState (secondChoiceLayout first second) 0 source := by
    exact choiceEntryState (secondChoiceLayout first second)
      inputLength payload (by
        simpa only [secondChoiceLayout] using
          (two_le_programRegisterSpan second))
  change
    runNPOracleProgram (taggedProgramChoice first second) maximumBits
        (sourceFuel + 1) (source.jump (choiceSecondBase first)) =
      some output
  rw [show choiceSecondBase first =
      (secondChoiceLayout first second).firstBase by rfl, hentry]
  apply run_continued
    (layout := secondChoiceLayout first second)
    (by
      simpa only [secondChoiceLayout] using
        (secondChoiceContinued first second))
    (le_refl (programRegisterSpan second))
    hsource
  intro haltState unused
  apply run_halt_instruction (choiceReturn first second)
  · rfl
  · simp [secondChoiceLayout, NPOracleState.write, NPOracleState.jump]
  · exact houtput

end NearCubicWires.TaggedProgramChoice
