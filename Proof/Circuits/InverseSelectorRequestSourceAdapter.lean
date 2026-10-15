import Proof.Circuits.FixedDescriptionRequestSourceAdapter
import Proof.Circuits.InverseLengthStage
import Proof.MachineModel.RuntimeCaseTwoRequestWordFrame

/-!
# Inverse request source tail at the selector-driven schedule

This is the inverse counterpart of the fixed request-source adapter.  The
source-driven bank emits the inverse selector's own scheduled registers; the
register-driven refuter frame and public source-word adapter then return
`pair sourceLength refuterWord`.  No schedule diagonal is used.
-/

namespace NearCubicWires.InverseSelectorRequestSourceAdapter

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

noncomputable def inverseTailSourceIndex
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  inverseSourceIndex
    (inverseSelectedSource contracts
      (publishedHierarchyOuterPCP contracts clockDepth)
      (inverseCoreAdvantagePower advantageExponent) target)

noncomputable def inverseTailSourceLength
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  sourceLength
    (inverseTailSourceIndex contracts clockDepth advantageExponent target)

noncomputable def inverseTailBankWidth
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseTailSourceIndex contracts clockDepth advantageExponent target)

noncomputable def inverseTailQueryCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
    (inverseTailSourceLength contracts clockDepth advantageExponent target)

noncomputable def inverseTailCopies
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseTailSourceIndex contracts clockDepth advantageExponent target)

noncomputable def inverseTailRefuterCode
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  encodeBitInput
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent target)

noncomputable def inverseTailSourceWordProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) : NPOracleProgram :=
  linkPrograms
    (publishedSourceDrivenBankProgram
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthProgram contracts clockDepth advantageExponent))
    (linkPrograms
      (bankRefuterWordFrameProgram
        (publishedRefuterSource contracts clockDepth).refuter.runner.program
        machine.description)
      sourceWordAdapterProgram)

noncomputable def inverseTailSourceWordBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  occurrenceStageBits target
    (publishedSourceDrivenBankBits
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent) target
      (inverseLengthBits contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseTailSourceLength contracts clockDepth advantageExponent target)
      target)
    (occurrenceStageBits target
      (bankRefuterWordFrameBits
        (publishedRefuterSource contracts clockDepth).refuter machine target
        (inverseTailSourceLength contracts clockDepth advantageExponent target)
        (inverseTailBankWidth contracts clockDepth advantageExponent target)
        (inverseTailQueryCount contracts clockDepth advantageExponent target)
        (inverseTailCopies contracts clockDepth advantageExponent target)
        target)
      (sourceWordAdapterBits
        (inverseTailRefuterCode contracts clockDepth machine advantageExponent
          target)
        (inverseTailSourceLength contracts clockDepth advantageExponent target)
        target))

noncomputable def inverseTailSourceWordFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  linkFuel
    (linkPrograms
      (bankRefuterWordFrameProgram
        (publishedRefuterSource contracts clockDepth).refuter.runner.program
        machine.description)
      sourceWordAdapterProgram)
    (publishedSourceDrivenBankFuel
      (publishedHierarchyOuterPCP contracts clockDepth)
      (publishedPointwisePCPP contracts)
      (inverseBankRate contracts advantageExponent)
      (inverseLengthFuel contracts clockDepth advantageExponent
        ⟨target, fixedTargetCodeInput target⟩)
      (inverseTailSourceLength contracts clockDepth advantageExponent target))
    (linkFuel sourceWordAdapterProgram
      (bankRefuterWordFrameFuel
        (publishedRefuterSource contracts clockDepth).refuter machine
        (inverseTailSourceLength contracts clockDepth advantageExponent target))
      sourceWordAdapterFuel)

set_option maxHeartbeats 800000 in
-- The selector bank and refuter frame carry the dependent scheduled word.
theorem run_inverseTailSourceWordProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (target : ℕ) :
    runNPOracleProgram
        (inverseTailSourceWordProgram contracts clockDepth machine
          advantageExponent)
        (inverseTailSourceWordBits contracts clockDepth machine
          advantageExponent target)
        (inverseTailSourceWordFuel contracts clockDepth machine
          advantageExponent target)
        (initialNPOracleState target target) =
      some
        (Nat.pair
          (inverseTailSourceLength contracts clockDepth advantageExponent
            target)
          (inverseTailRefuterCode contracts clockDepth machine
            advantageExponent target)) := by
  have hbank₀ := run_inverseSelectorBank_closed contracts clockDepth
    advantageExponent target (fixedTargetCodeInput target)
  have hlength :
      inverseScheduleLength contracts clockDepth advantageExponent target =
        inverseTailSourceLength contracts clockDepth advantageExponent target :=
    rfl
  rw [hlength] at hbank₀
  have hbank :
      runNPOracleProgram
          (publishedSourceDrivenBankProgram
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseLengthProgram contracts clockDepth advantageExponent))
          (publishedSourceDrivenBankBits
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent) target
            (inverseLengthBits contracts clockDepth advantageExponent
              ⟨target, fixedTargetCodeInput target⟩)
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target)
            target)
          (publishedSourceDrivenBankFuel
            (publishedHierarchyOuterPCP contracts clockDepth)
            (publishedPointwisePCPP contracts)
            (inverseBankRate contracts advantageExponent)
            (inverseLengthFuel contracts clockDepth advantageExponent
              ⟨target, fixedTargetCodeInput target⟩)
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target))
          (initialNPOracleState target target) =
        some
          (scheduleNumeralBankOutput
            (inverseTailSourceLength contracts clockDepth advantageExponent
              target)
            (inverseTailBankWidth contracts clockDepth advantageExponent target)
            (inverseTailQueryCount contracts clockDepth advantageExponent
              target)
            (inverseTailCopies contracts clockDepth advantageExponent target)
            target) := by
    simpa [inverseTailSourceLength, inverseTailSourceIndex,
      inverseTailBankWidth, inverseTailQueryCount, inverseTailCopies,
      selectorDrivenBankFrame] using hbank₀
  have hframe := run_bankRefuterWordFrameProgram
    (publishedRefuterSource contracts clockDepth).refuter machine target
    (inverseTailSourceLength contracts clockDepth advantageExponent target)
    (inverseTailBankWidth contracts clockDepth advantageExponent target)
    (inverseTailQueryCount contracts clockDepth advantageExponent target)
    (inverseTailCopies contracts clockDepth advantageExponent target) target
  have hadapter := run_sourceWordAdapterProgram target
    (inverseTailRefuterCode contracts clockDepth machine advantageExponent
      target)
    (inverseTailSourceLength contracts clockDepth advantageExponent target)
    target
  rw [inverseTailSourceWordProgram, inverseTailSourceWordBits,
    inverseTailSourceWordFuel]
  exact run_occurrenceStage hbank
    (run_occurrenceStage
      (by
        simpa [inverseTailRefuterCode, inverseRefuterInput,
          inverseTailSourceLength, inverseTailSourceIndex] using hframe)
      hadapter)

end NearCubicWires.InverseSelectorRequestSourceAdapter
