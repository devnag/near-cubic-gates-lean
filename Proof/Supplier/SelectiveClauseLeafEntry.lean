import Proof.Circuits.AmbientLinkEntry
import Proof.Supplier.SelectiveClauseRun

namespace NearCubicWires.BoundedOracleStructuralSelectiveProgram

open NearCubicWires
open NearCubicWires.AmbientLinkEntry
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.CanonicalEncodedListLookupProgram
open NearCubicWires.CanonicalLiteralDecodeProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

open private preserveRightLayout preserveRight_continued
  from Proof.MachineModel.PreserveRightProgram

open private run_encodedListLookupLoop
  from Proof.MachineModel.CanonicalEncodedListLookupProgram

open private relocateActiveState_self
  from Proof.Supplier.SelectiveCountCasesRun

open private structuralAddressProgram selectiveClauseProgram
  from Proof.MachineModel.BoundedOracleStructuralSelectiveProgram

open private projectedRandomBitAdapterProgram projectedRandomBitAdapterBound
  projectedRandomBitAdapterBits projectedRandomBitPreparedInput
  projectedRandomBitTag projectedRandomBitPayload projectedRandomBitIndex
  projectedRandomBitContext projectedRandomBitEvaluatorProgram
  projectedRandomBitEvaluatorBits projectedRandomBitEvaluatorFuel
  projectedRandomBitEvaluatedInput projectedRandomBitModRequests
  run_projectedRandomBitEvaluatorProgram run_bitSerialModProgram_zero
  from Proof.MachineModel.CanonicalProjectedRandomBitProgram

private theorem leafStateExt {left right : NPOracleState}
    (hpc : left.pc = right.pc) (hregisters : left.registers = right.registers) :
    left = right := by
  cases left
  cases right
  simp_all

/-! ## 1. The projected-bit adapter at an arbitrary entry state

The adapter is fourteen straight-line instructions that write every register
they read, so only the request in register zero matters. -/

private theorem run_projectedRandomBitAdapterProgram_anyEntry
    (width projectionCode randomnessCode : ℕ) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        projectedRandomBitInput width projectionCode randomnessCode) :
    runNPOracleProgram projectedRandomBitAdapterProgram
        (projectedRandomBitAdapterBits width projectionCode randomnessCode)
        14 entry =
      some
        (projectedRandomBitPreparedInput
          width projectionCode randomnessCode) := by
  let input :=
    projectedRandomBitInput width projectionCode randomnessCode
  let tag := projectedRandomBitTag projectionCode
  let payload := projectedRandomBitPayload projectionCode
  let leftRequest := bitSerialModInput payload width
  let rightRequest := bitSerialModInput tag 3
  let requests := Nat.pair leftRequest rightRequest
  let retained := Nat.pair randomnessCode payload
  let context := Nat.pair width retained
  let prepared := Nat.pair requests context
  let bound :=
    projectedRandomBitAdapterBound
      width projectionCode randomnessCode
  let bits :=
    projectedRandomBitAdapterBits
      width projectionCode randomnessCode
  have hinput : input ≤ bound := by
    exact Nat.le_max_left _ _
  have hprepared : prepared ≤ bound := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hthree : 3 ≤ bound := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hbitsOf : ∀ {value : ℕ}, value ≤ bound →
      natBitLength value ≤ bits := by
    intro value hvalue
    exact natBitLength_mono hvalue
  have hwidth : width ≤ bound := by
    exact (Nat.left_le_pair width
      (Nat.pair projectionCode randomnessCode)).trans hinput
  have hprojection : projectionCode ≤ bound := by
    exact
      (Nat.left_le_pair projectionCode randomnessCode).trans <|
        (Nat.right_le_pair width
          (Nat.pair projectionCode randomnessCode)).trans hinput
  have hrandomness : randomnessCode ≤ bound := by
    exact
      (Nat.right_le_pair projectionCode randomnessCode).trans <|
        (Nat.right_le_pair width
          (Nat.pair projectionCode randomnessCode)).trans hinput
  have htag : tag ≤ bound := by
    exact (Nat.unpair_left_le projectionCode).trans hprojection
  have hpayload : payload ≤ bound := by
    exact (Nat.unpair_right_le projectionCode).trans hprojection
  have hleftRequest : leftRequest ≤ bound := by
    exact (Nat.left_le_pair leftRequest rightRequest).trans <|
      (Nat.left_le_pair requests context).trans hprepared
  have hrightRequest : rightRequest ≤ bound := by
    exact (Nat.right_le_pair leftRequest rightRequest).trans <|
      (Nat.left_le_pair requests context).trans hprepared
  have hrequests : requests ≤ bound :=
    (Nat.left_le_pair requests context).trans hprepared
  have hretained : retained ≤ bound := by
    exact (Nat.right_le_pair width retained).trans <|
      (Nat.right_le_pair requests context).trans hprepared
  have hcontext : context ≤ bound :=
    (Nat.right_le_pair requests context).trans hprepared
  rw [show 14 = 13 + 1 by omega]
  rw [run_unpairLeft_instruction (value := width)
    (by rfl) hentryPc
    (by simp [hentryInput, projectedRandomBitInput])
    (hbitsOf hwidth)]
  rw [show 13 = 12 + 1 by omega]
  rw [run_unpairRight_instruction
    (value := Nat.pair projectionCode randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump, hentryInput,
      projectedRandomBitInput])
    (hbitsOf <|
      (Nat.right_le_pair width
        (Nat.pair projectionCode randomnessCode)).trans hinput)]
  rw [show 12 = 11 + 1 by omega]
  rw [run_unpairLeft_instruction (value := projectionCode)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump])
    (hbitsOf hprojection)]
  rw [show 11 = 10 + 1 by omega]
  rw [run_unpairRight_instruction (value := randomnessCode)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump])
    (hbitsOf hrandomness)]
  rw [show 10 = 9 + 1 by omega]
  rw [run_unpairLeft_instruction (value := tag)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, tag, projectedRandomBitTag])
    (hbitsOf htag)]
  rw [show 9 = 8 + 1 by omega]
  rw [run_unpairRight_instruction (value := payload)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, payload, projectedRandomBitPayload])
    (hbitsOf hpayload)]
  rw [show 8 = 7 + 1 by omega]
  rw [run_set_instruction (value := 3)
    (by rfl) rfl (hbitsOf hthree)]
  rw [show 7 = 6 + 1 by omega]
  rw [run_pair_instruction (value := leftRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, leftRequest, bitSerialModInput])
    (hbitsOf hleftRequest)]
  rw [show 6 = 5 + 1 by omega]
  rw [run_pair_instruction (value := rightRequest)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, rightRequest, bitSerialModInput])
    (hbitsOf hrightRequest)]
  rw [show 5 = 4 + 1 by omega]
  rw [run_pair_instruction (value := requests)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, requests])
    (hbitsOf hrequests)]
  rw [show 4 = 3 + 1 by omega]
  rw [run_pair_instruction (value := retained)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, retained])
    (hbitsOf hretained)]
  rw [show 3 = 2 + 1 by omega]
  rw [run_pair_instruction (value := context)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, context])
    (hbitsOf hcontext)]
  rw [show 2 = 1 + 1 by omega]
  rw [run_pair_instruction (value := prepared)
    (by rfl) rfl
    (by simp [NPOracleState.write,
      NPOracleState.jump, prepared])
    (hbitsOf hprepared)]
  have hpreparedEq :
      prepared =
        projectedRandomBitPreparedInput
          width projectionCode randomnessCode := by
    rfl
  rw [← hpreparedEq]
  exact run_halt_instruction (fuel := 0)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump])
    (hbitsOf hprepared)

/-! ## 2. The published projected-bit evaluator at an arbitrary entry state -/

set_option maxHeartbeats 1600000 in
-- Four nested register-width envelopes are re-derived at the entry's own
-- public length, so the width ledger alone exceeds the default budget.
/-- **The projected-bit evaluator, run on a relocated frame.**  The adapter of
§1 is entry independent, so `AmbientLinkEntry.run_linkPrograms_anyEntry`
carries the published run to any entry state whose register one is charged
against the advertised width. -/
theorem run_projectedRandomBitProgram_anyEntry
    (inputLength width projectionCode randomnessCode : ℕ)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        projectedRandomBitInput width projectionCode randomnessCode)
    (hentryLength :
      natBitLength (entry.registers 1) ≤
        projectedRandomBitBits inputLength width projectionCode
          randomnessCode) :
    runNPOracleProgram projectedRandomBitProgram
        (projectedRandomBitBits inputLength width projectionCode randomnessCode)
        (projectedRandomBitFuel width projectionCode randomnessCode) entry =
      some (projectedRandomBitOutput width projectionCode randomnessCode) := by
  let entryLength := entry.registers 1
  let payload := projectedRandomBitPayload projectionCode
  let tag := projectedRandomBitTag projectionCode
  let leftRequest := bitSerialModInput payload width
  let rightRequest := bitSerialModInput tag 3
  let leftOutput := projectedRandomBitIndex width projectionCode
  let rightOutput := tag % 3
  let context := projectedRandomBitContext width projectionCode randomnessCode
  let calls := Nat.pair leftRequest rightRequest
  let outputs := Nat.pair leftOutput rightOutput
  let pairedBits :=
    pairedCallBits entryLength (bitSerialModBits payload width)
      (bitSerialModBits tag 3) leftRequest rightRequest leftOutput rightOutput
  let pairedFuel :=
    pairedCallFuel bitSerialModProgram (bitSerialModFuel payload width)
      (bitSerialModFuel tag 3)
  let preservedBits := preserveRightBits pairedBits calls context outputs
  let preservedFuel := preserveRightFuel pairedFuel
  let evaluatorBits :=
    projectedRandomBitEvaluatorBits width projectionCode randomnessCode
  let evaluatorFuel :=
    projectedRandomBitEvaluatorFuel width projectionCode randomnessCode
  let maximumBits :=
    projectedRandomBitBits inputLength width projectionCode randomnessCode
  have hlength : natBitLength entryLength ≤ maximumBits := hentryLength
  have hadapterBits :
      projectedRandomBitAdapterBits width projectionCode randomnessCode ≤
        maximumBits := by
    simp [maximumBits, projectedRandomBitBits]
  have hpublishedBits :
      preserveRightBits
          (pairedCallBits inputLength (bitSerialModBits payload width)
            (bitSerialModBits tag 3) leftRequest rightRequest leftOutput
            rightOutput)
          calls context outputs ≤
        maximumBits := by
    simp [maximumBits, projectedRandomBitBits, payload, tag,
      leftRequest, rightRequest, leftOutput, rightOutput, context, calls,
      outputs]
  have hpreservedBits : preservedBits ≤ maximumBits := by
    simp only [preservedBits, pairedBits, preserveRightBits,
      pairedCallBits] at hpublishedBits ⊢
    omega
  have hevaluatorBits : evaluatorBits ≤ maximumBits := by
    simp [maximumBits, projectedRandomBitBits, evaluatorBits]
  have hpositive : 1 ≤ maximumBits :=
    (show 1 ≤ natBitLength entryLength by
      unfold natBitLength
      omega).trans hlength
  have hleft :
      runNPOracleProgram bitSerialModProgram (bitSerialModBits payload width)
          (bitSerialModFuel payload width)
          (initialNPOracleState entryLength leftRequest) =
        some leftOutput := by
    by_cases hwidthZero : width = 0
    · subst width
      simpa [leftRequest, leftOutput, projectedRandomBitIndex] using
        (run_bitSerialModProgram_zero entryLength payload)
    · have hrun :=
        run_bitSerialModProgram entryLength payload width
          (Nat.pos_of_ne_zero hwidthZero)
      simpa [leftRequest, leftOutput, projectedRandomBitIndex, hwidthZero]
        using hrun
  have hright :
      runNPOracleProgram bitSerialModProgram (bitSerialModBits tag 3)
          (bitSerialModFuel tag 3)
          (initialNPOracleState entryLength rightRequest) =
        some rightOutput := by
    simpa [rightRequest, rightOutput] using
      (run_bitSerialModProgram entryLength tag 3 (by omega))
  have hpaired :
      runNPOracleProgram (pairedCallProgram bitSerialModProgram) pairedBits
          pairedFuel (initialNPOracleState entryLength calls) =
        some outputs :=
    run_pairedCallProgram bitSerialModProgram entryLength
      (bitSerialModBits payload width) (bitSerialModBits tag 3)
      (bitSerialModFuel payload width) (bitSerialModFuel tag 3) leftRequest
      rightRequest leftOutput rightOutput hleft hright
  have hpreservedOwn :
      runNPOracleProgram (preserveRightProgram <|
            pairedCallProgram bitSerialModProgram)
          preservedBits preservedFuel
          (initialNPOracleState entryLength (Nat.pair calls context)) =
        some (Nat.pair outputs context) :=
    run_preserveRightProgram (pairedCallProgram bitSerialModProgram)
      entryLength pairedBits pairedFuel calls context outputs hpaired
  have hpreserved :
      runNPOracleProgram (preserveRightProgram <|
            pairedCallProgram bitSerialModProgram)
          maximumBits preservedFuel
          (initialNPOracleState entryLength
            (projectedRandomBitPreparedInput width projectionCode
              randomnessCode)) =
        some
          (projectedRandomBitEvaluatedInput width projectionCode
            randomnessCode) := by
    have hrun := run_bits_mono hpreservedOwn hpreservedBits
    simpa [projectedRandomBitPreparedInput, projectedRandomBitModRequests,
      projectedRandomBitEvaluatedInput, payload, tag, leftRequest, rightRequest,
      leftOutput, rightOutput, context, calls, outputs] using hrun
  have hevaluator :
      runNPOracleProgram projectedRandomBitEvaluatorProgram maximumBits
          evaluatorFuel
          (initialNPOracleState entryLength
            (projectedRandomBitEvaluatedInput width projectionCode
              randomnessCode)) =
        some (projectedRandomBitOutput width projectionCode randomnessCode) :=
    run_bits_mono
      (run_projectedRandomBitEvaluatorProgram entryLength width projectionCode
        randomnessCode)
      hevaluatorBits
  have hinner :
      runNPOracleProgram
          (linkPrograms
            (preserveRightProgram <| pairedCallProgram bitSerialModProgram)
            projectedRandomBitEvaluatorProgram)
          maximumBits
          (linkFuel projectedRandomBitEvaluatorProgram preservedFuel
            evaluatorFuel)
          (initialNPOracleState entryLength
            (projectedRandomBitPreparedInput width projectionCode
              randomnessCode)) =
        some (projectedRandomBitOutput width projectionCode randomnessCode) :=
    run_linkPrograms hpositive hlength hpreserved hevaluator
  have hrun :
      runNPOracleProgram
          (linkPrograms projectedRandomBitAdapterProgram
            (linkPrograms
              (preserveRightProgram <| pairedCallProgram bitSerialModProgram)
              projectedRandomBitEvaluatorProgram))
          maximumBits
          (linkFuel
            (linkPrograms
              (preserveRightProgram <| pairedCallProgram bitSerialModProgram)
              projectedRandomBitEvaluatorProgram)
            14
            (linkFuel projectedRandomBitEvaluatorProgram preservedFuel
              evaluatorFuel))
          entry =
        some (projectedRandomBitOutput width projectionCode randomnessCode) := by
    refine run_linkPrograms_anyEntry hpositive entry hentryPc hentryInput
      hentryLength ?_ hinner
    intro state hstatePc hstateInput _
    exact run_bits_mono
      (run_projectedRandomBitAdapterProgram_anyEntry width projectionCode
        randomnessCode state hstatePc hstateInput)
      hadapterBits
  simpa [projectedRandomBitProgram, projectedRandomBitFuel, maximumBits,
    payload, tag, pairedFuel, preservedFuel, evaluatorFuel] using hrun

/-- **The projected-bit entry premise, discharged.** -/
theorem projectedRandomBitEntryRunner : ProjectedRandomBitEntryRunner where
  executes := by
    intro inputLength width projectionCode randomnessCode entry hentryPc
      hentryInput hentryLength
    exact run_projectedRandomBitProgram_anyEntry inputLength width
      projectionCode randomnessCode entry hentryPc hentryInput hentryLength

/-! ## 3. The count-preserving adapter at an arbitrary entry state

`preserveRightProgram` parses the request pair, runs its source on the left
component, and re-pairs the retained right component.  Only the two parsing
writes stand between the entry state and the source, so an entry-independent
source lifts to an entry-independent adapter. -/

theorem run_preserveRightProgram_anyEntry (source : NPOracleProgram)
    (sourceBits sourceFuel left right output : ℕ) (entry : NPOracleState)
    (hentryPc : entry.pc = 0)
    (hentryInput : entry.registers 0 = Nat.pair left right)
    (hsource : ∀ state : NPOracleState, state.pc = 0 →
      state.registers 0 = left → state.registers 1 = entry.registers 1 →
      runNPOracleProgram source sourceBits sourceFuel state = some output) :
    runNPOracleProgram (preserveRightProgram source)
        (preserveRightBits sourceBits left right output)
        (preserveRightFuel sourceFuel) entry =
      some (Nat.pair output right) := by
  have hspan : 2 ≤ programRegisterSpan source :=
    two_le_programRegisterSpan source
  have hsourceBits : sourceBits ≤ preserveRightBits sourceBits left right output :=
    Nat.le_max_left _ _
  have hinputBits :
      natBitLength (Nat.pair left right) ≤
        preserveRightBits sourceBits left right output :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have houtputBits :
      natBitLength (Nat.pair output right) ≤
        preserveRightBits sourceBits left right output :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hleftBits :
      natBitLength left ≤ preserveRightBits sourceBits left right output :=
    (natBitLength_mono (Nat.left_le_pair left right)).trans hinputBits
  have hrightBits :
      natBitLength right ≤ preserveRightBits sourceBits left right output :=
    (natBitLength_mono (Nat.right_le_pair left right)).trans hinputBits
  obtain ⟨sourceEntry, hsourceEntryPc, hsourceEntryRegisters⟩ :
      ∃ state : NPOracleState, state.pc = 0 ∧ ∀ candidate,
        state.registers candidate =
          if candidate = 0 then left else entry.registers candidate :=
    ⟨{ pc := 0
       registers := fun candidate =>
         if candidate = 0 then left else entry.registers candidate }, rfl,
      fun _ => rfl⟩
  have hsourceRun :
      runNPOracleProgram source
          (preserveRightBits sourceBits left right output) sourceFuel
          sourceEntry =
        some output := by
    refine run_bits_mono (hsource sourceEntry hsourceEntryPc ?_ ?_) hsourceBits
    · rw [hsourceEntryRegisters, if_pos rfl]
    · rw [hsourceEntryRegisters, if_neg (by omega)]
  rw [show preserveRightFuel sourceFuel = ((sourceFuel + 2) + 1) + 1 by
    simp only [preserveRightFuel]]
  rw [run_unpairRight_instruction
    (program := preserveRightProgram source) (pc := 0) (source := 0)
    (destination := (preserveRightLayout source).savedLengthRegister)
    (next := 1) (value := right)
    (by simp [preserveRightProgram]) hentryPc
    (by simp [hentryInput]) hrightBits]
  rw [run_unpairLeft_instruction
    (program := preserveRightProgram source) (pc := 1) (source := 0)
    (destination := 0) (next := (preserveRightLayout source).firstBase)
    (value := left)
    (by simp [preserveRightProgram]) rfl
    (by
      simp only [NPOracleState.write, NPOracleState.jump]
      rw [if_neg (by simp only [preserveRightLayout]; omega)]
      simp [hentryInput])
    hleftBits]
  rw [show
      ((((entry.write (preserveRightLayout source).savedLengthRegister
        right).jump 1).write 0 left).jump
          (preserveRightLayout source).firstBase) =
      firstStageStateAt (preserveRightLayout source)
        (fun candidate =>
          if candidate = (preserveRightLayout source).savedLengthRegister then
            right else entry.registers candidate)
        sourceEntry by
    refine leafStateExt ?_ ?_
    · simp [firstStageStateAt, NPOracleState.jump, hsourceEntryPc]
    · funext candidate
      by_cases hlow : candidate < (preserveRightLayout source).firstSpan
      · have hne :
            candidate ≠ (preserveRightLayout source).savedLengthRegister := by
          simp only [preserveRightLayout] at hlow ⊢
          omega
        simp [firstStageStateAt, NPOracleState.jump, NPOracleState.write,
          hsourceEntryRegisters, hlow, hne]
      · have hne : candidate ≠ 0 := by
          simp only [preserveRightLayout] at hlow
          omega
        simp [firstStageStateAt, NPOracleState.jump, NPOracleState.write,
          hsourceEntryRegisters, hlow, hne]]
  refine run_continuedAt (preserveRight_continued source)
    (le_refl (programRegisterSpan source)) hsourceRun ?_
  intro haltState unused
  rw [show unused + 2 = (unused + 1) + 1 by omega]
  rw [run_pair_instruction
    (program := preserveRightProgram source)
    (pc := (preserveRightLayout source).resetBase)
    (left := (preserveRightLayout source).transferRegister)
    (right := (preserveRightLayout source).savedLengthRegister)
    (destination := 0)
    (next := (preserveRightLayout source).resetBase + 1)
    (value := Nat.pair output right)
    (by simp [preserveRightProgram, preserveRightLayout]) rfl
    (by
      simp only [NPOracleState.jump, NPOracleState.write]
      simp only [if_true]
      rw [if_neg (by simp [preserveRightLayout])]
      simp only [firstStageStateAt]
      simp [preserveRightLayout])
    houtputBits]
  refine run_halt_instruction
    (program := preserveRightProgram source)
    (pc := (preserveRightLayout source).resetBase + 1)
    (outputRegister := 0) (value := Nat.pair output right)
    (by simp [preserveRightProgram, preserveRightLayout]) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-! ## 4. The published literal decoder at an arbitrary entry state -/

theorem run_encodedListLookupProgram_anyEntry (code index fallback : ℕ)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 = encodedListLookupInput code index fallback) :
    runNPOracleProgram encodedListLookupProgram
        (encodedListLookupBits code index fallback)
        (encodedListLookupFuel code index) entry =
      some (encodedListGetD code index fallback) := by
  have hrequestBits :
      natBitLength (encodedListLookupInput code index fallback) ≤
        encodedListLookupBits code index fallback := le_refl _
  have hcodeBits :
      natBitLength code ≤ encodedListLookupBits code index fallback :=
    (natBitLength_mono <| by
      simpa only [encodedListLookupInput] using
        Nat.left_le_pair code (Nat.pair index fallback)).trans hrequestBits
  have hfieldsBits :
      natBitLength (Nat.pair index fallback) ≤
        encodedListLookupBits code index fallback :=
    (natBitLength_mono <| by
      simpa only [encodedListLookupInput] using
        Nat.right_le_pair code (Nat.pair index fallback)).trans hrequestBits
  have hindexBits :
      natBitLength index ≤ encodedListLookupBits code index fallback :=
    (natBitLength_mono (Nat.left_le_pair index fallback)).trans hfieldsBits
  have hfallbackBits :
      natBitLength fallback ≤ encodedListLookupBits code index fallback :=
    (natBitLength_mono (Nat.right_le_pair index fallback)).trans hfieldsBits
  rw [show encodedListLookupFuel code index =
      (3 + encodedListLookupLoopFuel code index) + 1 by
    unfold encodedListLookupFuel
    omega]
  rw [run_unpairLeft_instruction (value := code)
    (by rfl) hentryPc
    (by simp [hentryInput, encodedListLookupInput]) hcodeBits]
  rw [show 3 + encodedListLookupLoopFuel code index =
    (2 + encodedListLookupLoopFuel code index) + 1 by omega]
  rw [run_unpairRight_instruction (value := Nat.pair index fallback)
    (by rfl) rfl
    (by
      simp [NPOracleState.write, NPOracleState.jump, hentryInput,
        encodedListLookupInput])
    hfieldsBits]
  rw [show 2 + encodedListLookupLoopFuel code index =
    (1 + encodedListLookupLoopFuel code index) + 1 by omega]
  rw [run_unpairLeft_instruction (value := index)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump]) hindexBits]
  rw [show 1 + encodedListLookupLoopFuel code index =
    encodedListLookupLoopFuel code index + 1 by omega]
  rw [run_unpairRight_instruction (value := fallback)
    (by rfl) rfl (by simp [NPOracleState.write, NPOracleState.jump])
    hfallbackBits]
  refine run_encodedListLookupLoop code index fallback _ _ rfl ?_ ?_ ?_
    hcodeBits hindexBits hfallbackBits
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 5. The two-level lookup at an arbitrary entry state -/

theorem run_encodedNestedListLookupProgram_anyEntry
    (inputLength code outerIndex innerIndex fallback : ℕ)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 =
        encodedNestedListLookupInput code outerIndex innerIndex fallback)
    (hentryLength :
      natBitLength (entry.registers 1) ≤
        encodedNestedListLookupBits inputLength code outerIndex innerIndex
          fallback) :
    runNPOracleProgram encodedNestedListLookupProgram
        (encodedNestedListLookupBits inputLength code outerIndex innerIndex
          fallback)
        (encodedNestedListLookupFuel code outerIndex innerIndex) entry =
      some (encodedNestedListGetD code outerIndex innerIndex fallback) := by
  have hfirstBits :
      preserveRightBits (encodedListLookupBits code outerIndex 0)
          (encodedListLookupInput code outerIndex 0)
          (Nat.pair innerIndex fallback)
          (encodedListGetD code outerIndex 0) ≤
        encodedNestedListLookupBits inputLength code outerIndex innerIndex
          fallback :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hsecondBits :
      encodedListLookupBits (encodedListGetD code outerIndex 0) innerIndex
          fallback ≤
        encodedNestedListLookupBits inputLength code outerIndex innerIndex
          fallback :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hpositive :
      1 ≤
        encodedNestedListLookupBits inputLength code outerIndex innerIndex
          fallback :=
    (show 1 ≤ natBitLength (entry.registers 1) by
      unfold natBitLength
      omega).trans hentryLength
  have hsecond :
      runNPOracleProgram encodedListLookupProgram
          (encodedNestedListLookupBits inputLength code outerIndex innerIndex
            fallback)
          (encodedListLookupFuel (encodedListGetD code outerIndex 0) innerIndex)
          (initialNPOracleState (entry.registers 1)
            (Nat.pair (encodedListGetD code outerIndex 0)
              (Nat.pair innerIndex fallback))) =
        some
          (encodedListGetD (encodedListGetD code outerIndex 0) innerIndex
            fallback) := by
    have hrun :=
      run_bits_mono
        (run_encodedListLookupProgram (entry.registers 1)
          (encodedListGetD code outerIndex 0) innerIndex fallback)
        hsecondBits
    simpa only [encodedListLookupInput] using hrun
  refine run_linkPrograms_anyEntry hpositive entry hentryPc hentryInput
    hentryLength ?_ hsecond
  intro state hstatePc hstateInput hstateLength
  refine run_bits_mono
    (run_preserveRightProgram_anyEntry encodedListLookupProgram
      (encodedListLookupBits code outerIndex 0)
      (encodedListLookupFuel code outerIndex)
      (encodedListLookupInput code outerIndex 0) (Nat.pair innerIndex fallback)
      (encodedListGetD code outerIndex 0) state hstatePc hstateInput ?_)
    hfirstBits
  intro inner hinnerPc hinnerInput _
  exact run_encodedListLookupProgram_anyEntry code outerIndex 0 inner hinnerPc
    hinnerInput

/-! ## 6. The published literal decoder, run on a relocated frame -/

set_option maxHeartbeats 1600000 in
-- The two nested width envelopes are re-derived at the entry's own public
-- length, so the ledger alone exceeds the default budget.
/-- **The literal decoder, run on a relocated frame.**  Both stages below the
link are entry independent — §4 for the list cursor, §3 for the adapter that
carries the arity — so `AmbientLinkEntry.run_linkPrograms_anyEntry` applies. -/
theorem run_threeCNFLiteralProgram_anyEntry
    (inputLength arity code clauseIndex position : ℕ) (harity : 0 < arity)
    (entry : NPOracleState) (hentryPc : entry.pc = 0)
    (hentryInput :
      entry.registers 0 = threeCNFLiteralInput arity code clauseIndex position)
    (hentryLength :
      natBitLength (entry.registers 1) ≤
        threeCNFLiteralBits inputLength arity code clauseIndex position) :
    runNPOracleProgram threeCNFLiteralProgram
        (threeCNFLiteralBits inputLength arity code clauseIndex position)
        (threeCNFLiteralFuel arity code clauseIndex position) entry =
      some (threeCNFLiteralOutput arity code clauseIndex position) := by
  have hpublishedWrapped :
      preserveRightBits
          (encodedNestedListLookupBits inputLength code clauseIndex position 0)
          (encodedNestedListLookupInput code clauseIndex position 0) arity
          (threeCNFLiteralRawCode code clauseIndex position) ≤
        threeCNFLiteralBits inputLength arity code clauseIndex position :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hpublishedDecode :
      literalDecodeBits inputLength arity
          (threeCNFLiteralRawCode code clauseIndex position) ≤
        threeCNFLiteralBits inputLength arity code clauseIndex position :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hwrappedBits :
      preserveRightBits
          (encodedNestedListLookupBits (entry.registers 1) code clauseIndex
            position 0)
          (encodedNestedListLookupInput code clauseIndex position 0) arity
          (threeCNFLiteralRawCode code clauseIndex position) ≤
        threeCNFLiteralBits inputLength arity code clauseIndex position := by
    simp only [preserveRightBits,
      encodedNestedListLookupBits] at hpublishedWrapped ⊢
    omega
  have hdecodeBits :
      literalDecodeBits (entry.registers 1) arity
          (threeCNFLiteralRawCode code clauseIndex position) ≤
        threeCNFLiteralBits inputLength arity code clauseIndex position := by
    simp only [literalDecodeBits] at hpublishedDecode ⊢
    omega
  have hpositive :
      1 ≤ threeCNFLiteralBits inputLength arity code clauseIndex position :=
    (show 1 ≤ natBitLength (entry.registers 1) by
      unfold natBitLength
      omega).trans hentryLength
  have hdecode :
      runNPOracleProgram literalDecodeProgram
          (threeCNFLiteralBits inputLength arity code clauseIndex position)
          (literalDecodeFuel arity
            (threeCNFLiteralRawCode code clauseIndex position))
          (initialNPOracleState (entry.registers 1)
            (Nat.pair (threeCNFLiteralRawCode code clauseIndex position)
              arity)) =
        some
          (threeCNFLiteralOutput arity code clauseIndex position) := by
    have hrun :=
      run_bits_mono
        (run_literalDecodeProgram (entry.registers 1) arity
          (threeCNFLiteralRawCode code clauseIndex position) harity)
        hdecodeBits
    simpa only [literalDecodeInput, threeCNFLiteralOutput] using hrun
  refine run_linkPrograms_anyEntry (first :=
      preserveRightProgram encodedNestedListLookupProgram)
    (second := literalDecodeProgram) hpositive entry hentryPc hentryInput
    hentryLength ?_ hdecode
  intro state hstatePc hstateInput hstateLength
  refine run_bits_mono
    (run_preserveRightProgram_anyEntry encodedNestedListLookupProgram
      (encodedNestedListLookupBits (entry.registers 1) code clauseIndex
        position 0)
      (encodedNestedListLookupFuel code clauseIndex position)
      (encodedNestedListLookupInput code clauseIndex position 0) arity
      (threeCNFLiteralRawCode code clauseIndex position) state hstatePc
      hstateInput ?_)
    hwrappedBits
  intro inner hinnerPc hinnerInput hinnerLength
  refine run_encodedNestedListLookupProgram_anyEntry (entry.registers 1) code
    clauseIndex position 0 inner hinnerPc hinnerInput ?_
  rw [hinnerLength, hstateLength]
  exact Nat.le_max_left _ _

/-- **The literal entry premise, discharged.** -/
theorem threeCNFLiteralEntryRunner : ThreeCNFLiteralEntryRunner where
  executes := by
    intro inputLength arity code clauseIndex position harity entry hentryPc
      hentryInput hentryLength
    exact run_threeCNFLiteralProgram_anyEntry inputLength arity code clauseIndex
      position harity entry hentryPc hentryInput hentryLength

/-! ## 7. Relocated calls that publish the callee frame's saved length

`SelectiveCountCasesRun.run_selectiveRelocatedCall` hands the callee an entry
state constrained only at the request register, which is not enough to apply
either premise of §2 and §6: both charge the callee frame's register one
against the advertised width.  The variant below exposes that register too.
Nothing else changes — the call site is the same physical block — so a
controller that writes the callee frame's register one before jumping (as the
address and clause controllers do, with one `set` instruction in place of a
coincident-target branch) discharges the side condition as
`natBitLength 0 ≤ bits`. -/

theorem run_selectiveRelocatedCall_frame
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
      entry.registers 1 = machine.registers (registerOffset + 1) →
      runNPOracleProgram source maximumBits calleeFuel entry =
        some calleeOutput)
    (haccumulatorZero : machine.registers accumulator = 0)
    (hpairBits : natBitLength (Nat.pair 0 calleeOutput) ≤ maximumBits)
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
    (hcallee _ rfl (by simp) (by simp)) ?_ ?_
  · rw [haccumulatorZero]
    exact hpairBits
  · intro haltState unused
    rw [Nat.add_comm unused extraFuel, haccumulatorZero]
    exact run_fuel_add (hreturn haltState) unused

/-! ## 8. The two repaired link call sites

Both level programs reach a `linkPrograms` callee through one physical block
that ends in a single instruction: it zeroes the callee frame's register one
and falls into the callee base.  The two decodes below pin that instruction, so
the controller traces of levels `11` and `12` can supply `§7`'s frame
hypothesis as `natBitLength 0 ≤ bits`. -/

/-- The address controller's projected-bit call site: the callee is relocated at
register base `2000` and program counter `38`. -/
theorem structuralAddressProgram_projectedBitLink :
    structuralAddressProgram[18]? = some (.set 2001 0 38) :=
  structuralAddressProgram_controllerAt (pc := 18) rfl

/-- The clause controller's literal call site: the callee is relocated at
register base `1000` and program counter `76`. -/
theorem selectiveClauseProgram_literalLink :
    selectiveClauseProgram[22]? = some (.set 1001 0 76) :=
  selectiveClauseProgram_controllerAt (pc := 22) rfl

end NearCubicWires.BoundedOracleStructuralSelectiveProgram
