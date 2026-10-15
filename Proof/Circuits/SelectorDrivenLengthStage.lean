import Proof.MachineModel.CanonicalTwoPowProgram
import Proof.MachineModel.SourceDrivenNumeralBank

/-!
# The length stage that discharges the source-driven bank's residual

`SourceDrivenNumeralBank` reduced both roots' diagonal to one purely executable
obligation: a program that emits `Nat.pair (scheduleLength …) code` from the
request (`FixedScheduledLengthRuns` / `InverseScheduledLengthRuns`).  That
obligation is *satisfiable* — unlike every form of `hdiagonal` — because the
schedule's index is exactly what the envelope's executable selector computes.

This module builds the supplier on the **fixed** schedule, where no
`inverseSourceIndex` scan is needed:
`FixedScheduleAtomLoop.fixedScheduleLength` is `sourceLength` of the selected
source itself, so the length is

```
requestCode ↦ encodeUnary length      (build the selector's unary request)
            ↦ selector output          (ScheduledRecovery.run_selector)
            ↦ source + 1               (extract .source, increment)
            ↦ 2 ^ (source + 1)         (CanonicalTwoPowProgram)
```

with the request code preserved on the right of the frame throughout by
`PreserveRightProgram`.  §1 is the unary builder, §2 the source extractor, §3
the assembled program and its run, §4 the discharged `FixedScheduledLengthRuns`.

The inverse schedule's supplier is the same pipeline with one extra stage — the
`RecoveryScheduleEnvelope.inverseSourceIndex` bounded scan — inserted between the
extractor and the two-power; that stage is named at the end of §4.
-/

namespace NearCubicWires.SelectorDrivenLengthStage

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 0. `encodeUnary` bookkeeping -/

private theorem encodeUnary_mono {left right : ℕ} (hle : left ≤ right) :
    encodeUnary left ≤ encodeUnary right := by
  induction right, hle using Nat.le_induction with
  | base => exact le_refl _
  | succ step _ ih =>
      exact ih.trans (by
        rw [show encodeUnary (step + 1) = Nat.pair 1 (encodeUnary step) from rfl]
        exact Nat.right_le_pair 1 (encodeUnary step))

/-! ## 1. The unary request builder

From `initialNPOracleState length code` emit `Nat.pair (encodeUnary length)
code`: the exact request state `ScheduledRecovery.run_selector` reads, with the
request code retained on the right.
-/

/-- Register ABI: `r0` request code (retained), `r2` countdown from the public
length, `r3` the accumulating unary encoding, `r4` the constant one. -/
def unaryBuildProgram : NPOracleProgram :=
  [ .copy 1 2 1
  , .set 3 0 2
  , .set 4 1 3
  , .branchZero 2 6 4
  , .decrement 2 5
  , .pair 4 3 3 3
  , .pair 3 0 0 7
  , .halt 0
  ]

@[simp] theorem unaryBuildProgram_oracleFree : OracleFree unaryBuildProgram := by
  rfl

def unaryBuildBits (length code : ℕ) : ℕ :=
  max (natBitLength (Nat.pair (encodeUnary length) code)) (natBitLength length)

def unaryBuildFuel (length : ℕ) : ℕ := 3 * length + 6

private theorem run_unaryBuildLoop (length code maximumBits : ℕ)
    (hpair :
      natBitLength (Nat.pair (encodeUnary length) code) ≤ maximumBits)
    (hlength : natBitLength length ≤ maximumBits) :
    ∀ (remaining built : ℕ) (state : NPOracleState),
      built + remaining = length →
      state.pc = 3 →
      state.registers 0 = code →
      state.registers 2 = remaining →
      state.registers 3 = encodeUnary built →
      state.registers 4 = 1 →
      runNPOracleProgram unaryBuildProgram maximumBits (3 * remaining + 3)
          state =
        some (Nat.pair (encodeUnary length) code) := by
  have honeBits : natBitLength 1 ≤ maximumBits := by
    have hmaxPos : 1 ≤ maximumBits :=
      le_trans (by unfold natBitLength; omega) hpair
    have hone : natBitLength 1 = 1 := by unfold natBitLength; simp
    omega
  intro remaining
  induction remaining with
  | zero =>
      intro built state hsum hpc _hcode hremaining hacc _hone
      have hbuilt : built = length := by omega
      have houtputBits :
          natBitLength (Nat.pair (encodeUnary built) code) ≤ maximumBits := by
        rw [hbuilt]; exact hpair
      rw [show 3 * 0 + 3 = 2 + 1 by omega]
      rw [run_branchZero_instruction (register := 2)
        (zeroTarget := 6) (nonzeroTarget := 4) (by rfl) hpc]
      have hjump :
          (state.jump (if state.registers 2 = 0 then 6 else 4)).pc = 6 := by
        simp [NPOracleState.jump, hremaining]
      rw [show 2 = 1 + 1 by omega]
      rw [run_pair_instruction (left := 3) (right := 0)
        (value := Nat.pair (encodeUnary built) code) (by rfl) hjump
        (by simp [NPOracleState.jump, hacc, _hcode]) houtputBits]
      rw [hbuilt]
      exact run_halt_instruction (fuel := 0)
        (value := Nat.pair (encodeUnary length) code) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump]) hpair
  | succ predecessor ih =>
      intro built state hsum hpc hcode hremaining hacc hone
      have hbuiltLt : built + 1 ≤ length := by omega
      have haccBits : natBitLength (encodeUnary built) ≤ maximumBits :=
        (natBitLength_mono ((encodeUnary_mono (by omega)).trans
          (Nat.left_le_pair (encodeUnary length) code))).trans hpair
      have hpredBits : natBitLength predecessor ≤ maximumBits :=
        (natBitLength_mono (by omega)).trans hlength
      have hnextAccBits :
          natBitLength (Nat.pair 1 (encodeUnary built)) ≤ maximumBits := by
        have hle : Nat.pair 1 (encodeUnary built) ≤ encodeUnary length := by
          rw [show Nat.pair 1 (encodeUnary built) = encodeUnary (built + 1)
            from rfl]
          exact encodeUnary_mono hbuiltLt
        exact (natBitLength_mono
          (hle.trans (Nat.left_le_pair (encodeUnary length) code))).trans hpair
      rw [show 3 * (predecessor + 1) + 3 = 3 * predecessor + 3 + 1 + 1 + 1 by
        omega]
      rw [run_branchZero_instruction (register := 2)
        (zeroTarget := 6) (nonzeroTarget := 4) (by rfl) hpc]
      have hjump :
          (state.jump (if state.registers 2 = 0 then 6 else 4)).pc = 4 := by
        simp [NPOracleState.jump, hremaining]
      rw [run_decrement_instruction (value := predecessor) (by rfl) hjump
        (by simp [NPOracleState.jump, hremaining]) hpredBits]
      rw [run_pair_instruction (left := 4) (right := 3)
        (value := Nat.pair 1 (encodeUnary built)) (by rfl) rfl
        (by simp [NPOracleState.write, NPOracleState.jump, hone, hacc])
        hnextAccBits]
      refine ih (built + 1) _ (by omega) rfl ?_ ?_ ?_ ?_
      · simp [NPOracleState.write, NPOracleState.jump, hcode]
      · simp [NPOracleState.write, NPOracleState.jump]
      · simp [NPOracleState.write, NPOracleState.jump]
        rfl
      · simp [NPOracleState.write, NPOracleState.jump, hone]

/-- **The unary request builder, executed.** -/
theorem run_unaryBuildProgram (length code : ℕ) :
    runNPOracleProgram unaryBuildProgram (unaryBuildBits length code)
        (unaryBuildFuel length) (initialNPOracleState length code) =
      some (Nat.pair (encodeUnary length) code) := by
  have hpair :
      natBitLength (Nat.pair (encodeUnary length) code) ≤
        unaryBuildBits length code :=
    Nat.le_max_left _ _
  have hlength : natBitLength length ≤ unaryBuildBits length code :=
    Nat.le_max_right _ _
  have hlengthBits :
      natBitLength length ≤ unaryBuildBits length code := hlength
  have hzeroBits : natBitLength 0 ≤ unaryBuildBits length code :=
    (natBitLength_mono (Nat.zero_le _)).trans hlength
  have honeBits : natBitLength 1 ≤ unaryBuildBits length code := by
    have hmaxPos : 1 ≤ unaryBuildBits length code :=
      le_trans (by unfold natBitLength; omega) hpair
    have hone : natBitLength 1 = 1 := by unfold natBitLength; simp
    omega
  unfold unaryBuildFuel
  rw [show 3 * length + 6 = 3 * length + 3 + 1 + 1 + 1 by omega]
  rw [run_copy_instruction (value := length) (by rfl) rfl
    (by simp [initialNPOracleState]) hlengthBits]
  rw [run_set_instruction (value := 0) (by rfl) rfl hzeroBits]
  rw [run_set_instruction (value := 1) (by rfl) rfl honeBits]
  refine run_unaryBuildLoop length code (unaryBuildBits length code) hpair
    hlength length 0 _ (by omega) rfl ?_ ?_ ?_ ?_
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump]
  · simp [NPOracleState.write, NPOracleState.jump]; rfl
  · simp [NPOracleState.write, NPOracleState.jump]

/-! ## 2. The source extractor

From `Nat.pair selectorCode code`, where `selectorCode` is a
`ScheduledRecovery.ExecutableScheduleSelection.code`, emit
`Nat.pair (source + 1) code`: the exponent the source length is a power of.
-/

/-- Register ABI: `r3` the selector code then the extracted source, `r4` the
retained request code. -/
def sourceIncrementProgram : NPOracleProgram :=
  [ .unpairLeft 0 3 1
  , .unpairRight 0 4 2
  , .unpairLeft 3 3 3
  , .increment 3 4
  , .pair 3 4 0 5
  , .halt 0
  ]

@[simp] theorem sourceIncrementProgram_oracleFree :
    OracleFree sourceIncrementProgram := by
  rfl

def sourceIncrementBits (source rest code : ℕ) : ℕ :=
  natBitLength
    (max (Nat.pair (Nat.pair source rest) code) (Nat.pair (source + 1) code))

/-- **The source extractor, executed.**  The selector code's left field is the
selected source, incremented to the exponent of its scheduled length. -/
theorem run_sourceIncrementProgram
    (inputLength source rest code : ℕ) :
    runNPOracleProgram sourceIncrementProgram
        (sourceIncrementBits source rest code) 6
        (initialNPOracleState inputLength
          (Nat.pair (Nat.pair source rest) code)) =
      some (Nat.pair (source + 1) code) := by
  have hframeBits :
      natBitLength (Nat.pair (Nat.pair source rest) code) ≤
        sourceIncrementBits source rest code :=
    natBitLength_mono (le_max_left _ _)
  have hselectorBits :
      natBitLength (Nat.pair source rest) ≤ sourceIncrementBits source rest code :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hframeBits
  have hcodeBits : natBitLength code ≤ sourceIncrementBits source rest code :=
    (natBitLength_mono (Nat.right_le_pair _ _)).trans hframeBits
  have hsourceBits :
      natBitLength source ≤ sourceIncrementBits source rest code :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans hselectorBits
  have houtputBits :
      natBitLength (Nat.pair (source + 1) code) ≤
        sourceIncrementBits source rest code :=
    natBitLength_mono (le_max_right _ _)
  have hsuccBits :
      natBitLength (source + 1) ≤ sourceIncrementBits source rest code :=
    (natBitLength_mono (Nat.left_le_pair _ _)).trans houtputBits
  rw [show (6 : ℕ) = 5 + 1 by omega]
  rw [run_unpairLeft_instruction (source := 0) (destination := 3)
    (value := Nat.pair source rest) (by rfl) rfl
    (by simp [initialNPOracleState]) hselectorBits]
  rw [show (5 : ℕ) = 4 + 1 by omega]
  rw [run_unpairRight_instruction (source := 0) (destination := 4)
    (value := code) (by rfl) rfl
    (by simp [initialNPOracleState, NPOracleState.write, NPOracleState.jump])
    hcodeBits]
  rw [show (4 : ℕ) = 3 + 1 by omega]
  rw [run_unpairLeft_instruction (source := 3) (destination := 3)
    (value := source) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsourceBits]
  rw [show (3 : ℕ) = 2 + 1 by omega]
  rw [run_increment_instruction (register := 3) (value := source + 1)
    (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) hsuccBits]
  rw [show (2 : ℕ) = 1 + 1 by omega]
  rw [run_pair_instruction (left := 3) (right := 4)
    (value := Nat.pair (source + 1) code) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits]
  exact run_halt_instruction (fuel := 0) (by rfl) rfl
    (by simp [NPOracleState.write, NPOracleState.jump]) houtputBits

/-! ## 3. The fixed schedule's length program, assembled -/

/-- The fixed schedule's executable selector at the published outer PCP. -/
noncomputable def fixedLengthSelectorProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ) :
    NPOracleProgram :=
  (fixedSchedule contracts (publishedHierarchyOuterPCP contracts clockDepth)
    requestedRate).selector.program

/-- **The fixed schedule's length program.**  Build the selector's unary
request, run the selector, extract the selected source, raise two to its
successor — the request code preserved on the right throughout. -/
noncomputable def fixedLengthProgram
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ) :
    NPOracleProgram :=
  linkPrograms unaryBuildProgram
    (linkPrograms
      (preserveRightProgram
        (fixedLengthSelectorProgram contracts clockDepth requestedRate))
      (linkPrograms sourceIncrementProgram
        (preserveRightProgram binaryTwoPowProgram)))

/-- The selected source at one target, named to keep the bits/fuel closed
forms compact. -/
noncomputable def fixedLengthSource
    (contracts : PublishedContracts) (clockDepth requestedRate target : ℕ) :
    ℕ :=
  fixedSelectedSource contracts
    (publishedHierarchyOuterPCP contracts clockDepth) requestedRate target

noncomputable def fixedLengthFuel
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  linkFuel
    (linkPrograms
      (preserveRightProgram
        (fixedLengthSelectorProgram contracts clockDepth requestedRate))
      (linkPrograms sourceIncrementProgram
        (preserveRightProgram binaryTwoPowProgram)))
    (unaryBuildFuel (LanguageEvaluationRequest.length request))
    (linkFuel
      (linkPrograms sourceIncrementProgram
        (preserveRightProgram binaryTwoPowProgram))
      (preserveRightFuel
        ((fixedSchedule contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          requestedRate).selector.budget
          (LanguageEvaluationRequest.length request)))
      (linkFuel (preserveRightProgram binaryTwoPowProgram) 6
        (preserveRightFuel
          (binaryTwoPowFuel
            (fixedLengthSource contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request) + 1)))))

noncomputable def fixedLengthBits
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (unaryBuildBits (LanguageEvaluationRequest.length request)
      (LanguageEvaluationRequest.code request))
    (occurrenceStageBits (LanguageEvaluationRequest.length request)
      (preserveRightBits
        ((fixedSchedule contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          requestedRate).selector.budget
          (LanguageEvaluationRequest.length request))
        (encodeUnary (LanguageEvaluationRequest.length request))
        (LanguageEvaluationRequest.code request)
        ((fixedSchedule contracts
          (publishedHierarchyOuterPCP contracts clockDepth)
          requestedRate).output (LanguageEvaluationRequest.length request)).code)
      (occurrenceStageBits (LanguageEvaluationRequest.length request)
        (sourceIncrementBits
          (fixedLengthSource contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request))
          (Nat.pair
            ((fixedSchedule contracts
              (publishedHierarchyOuterPCP contracts clockDepth)
              requestedRate).output
              (LanguageEvaluationRequest.length request)).nextSource
            (Nat.pair
              ((fixedSchedule contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                requestedRate).output
                (LanguageEvaluationRequest.length request)).core
              ((fixedSchedule contracts
                (publishedHierarchyOuterPCP contracts clockDepth)
                requestedRate).output
                (LanguageEvaluationRequest.length request)).nextCore))
          (LanguageEvaluationRequest.code request))
        (preserveRightBits
          (binaryTwoPowBits
            (fixedLengthSource contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request) + 1))
          (fixedLengthSource contracts clockDepth requestedRate
            (LanguageEvaluationRequest.length request) + 1)
          (LanguageEvaluationRequest.code request)
          (2 ^
            (fixedLengthSource contracts clockDepth requestedRate
              (LanguageEvaluationRequest.length request) + 1)))))

/-- **The fixed schedule's length program, executed.**  From the request it
emits the fixed chain's own scheduled source length, beside the retained
request code. -/
theorem run_fixedLengthProgram
    (contracts : PublishedContracts) (clockDepth requestedRate target : ℕ)
    (input : BitInput target) :
    runNPOracleProgram
        (fixedLengthProgram contracts clockDepth requestedRate)
        (fixedLengthBits contracts clockDepth requestedRate ⟨target, input⟩)
        (fixedLengthFuel contracts clockDepth requestedRate ⟨target, input⟩)
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (Nat.pair
          (fixedScheduleLength contracts clockDepth requestedRate target)
          (encodeBitInput input)) := by
  set schedule := fixedSchedule contracts
    (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
    with hschedule
  set code := encodeBitInput input with hcode
  set source := (schedule.output target).source with hsource
  have hlength :
      (2 : ℕ) ^ (source + 1) =
        fixedScheduleLength contracts clockDepth requestedRate target := rfl
  refine Eq.trans ?_ (congrArg (fun value => some (Nat.pair value code)) hlength)
  refine run_occurrenceStage
    (run_unaryBuildProgram target code)
    (run_occurrenceStage
      (run_preserveRightProgram
        (fixedLengthSelectorProgram contracts clockDepth requestedRate) target
        (schedule.selector.budget target) (schedule.selector.budget target)
        (encodeUnary target) code (schedule.output target).code
        (schedule.run_selector target))
      (run_occurrenceStage
        (run_sourceIncrementProgram target source
          (Nat.pair (schedule.output target).nextSource
            (Nat.pair (schedule.output target).core
              (schedule.output target).nextCore))
          code)
        (run_preserveRightProgram binaryTwoPowProgram target
          (binaryTwoPowBits (source + 1)) (binaryTwoPowFuel (source + 1))
          (source + 1) code (2 ^ (source + 1))
          (run_binaryTwoPowProgram target (source + 1)
            (binaryTwoPowBits (source + 1)) (le_refl _)))))

/-! ## 4. `FixedScheduledLengthRuns`, discharged -/

/-- **The fixed schedule's residual is a theorem.**  The obligation
`SourceDrivenNumeralBank` left — a program emitting the fixed chain's scheduled
source length — is met by `fixedLengthProgram`, with no schedule hypothesis and,
crucially, no `hdiagonal` in any form.  This is the fixed half of the diagonal
repair, fully closed at the length stage. -/
theorem fixed_scheduledLengthRuns
    (contracts : PublishedContracts) (clockDepth requestedRate : ℕ) :
    FixedScheduledLengthRuns contracts clockDepth requestedRate
      (fixedLengthProgram contracts clockDepth requestedRate)
      (fixedLengthBits contracts clockDepth requestedRate)
      (fixedLengthFuel contracts clockDepth requestedRate) :=
  fun target input => run_fixedLengthProgram contracts clockDepth requestedRate
    target input

/-- **The fixed schedule's selector-driven bank, closed.**  Composing the
length supplier with `SourceDrivenNumeralBank.run_fixedSelectorDrivenBankProgram`
emits the fixed chain's own frame at every request with **no hypothesis at
all** — no `hdiagonal`, no schedule premise.  The fixed half of the diagonal
repair is complete end to end. -/
theorem run_fixedSelectorBank_closed
    (contracts : PublishedContracts) (clockDepth requestedRate target : ℕ)
    (input : BitInput target) :
    runNPOracleProgram
        (publishedSourceDrivenBankProgram
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          (fixedLengthProgram contracts clockDepth requestedRate))
        (publishedSourceDrivenBankBits
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          target
          (fixedLengthBits contracts clockDepth requestedRate ⟨target, input⟩)
          (fixedScheduleLength contracts clockDepth requestedRate target)
          (encodeBitInput input))
        (publishedSourceDrivenBankFuel
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          (fixedLengthFuel contracts clockDepth requestedRate ⟨target, input⟩)
          (fixedScheduleLength contracts clockDepth requestedRate target))
        (initialNPOracleState target (encodeBitInput input)) =
      some
        (selectorDrivenBankFrame
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (UniformTargetLanguageBank.fixedBankRate contracts requestedRate)
          (fixedSelectedSource contracts
            (publishedHierarchyOuterPCP contracts clockDepth) requestedRate
            target)
          (encodeBitInput input)) :=
  run_fixedSelectorDrivenBankProgram contracts clockDepth requestedRate
    (fixedLengthProgram contracts clockDepth requestedRate)
    (fixedLengthBits contracts clockDepth requestedRate)
    (fixedLengthFuel contracts clockDepth requestedRate)
    (fixed_scheduledLengthRuns contracts clockDepth requestedRate) target input

end NearCubicWires.SelectorDrivenLengthStage
