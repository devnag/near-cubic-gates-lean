import Proof.Circuits.InverseSelectorAtomStreamClosure

/-!
# Frozen source-bank setup for the guarded selector atom stream

This module isolates the unchanged fixed-target source-driven bank.  The
guarded selector proof can consume its exact frame without reopening the
source schedule normalization.
-/

namespace NearCubicWires.TotalInverseSelectorAtomStreamSourceBank

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedDescriptionRequestSourceAdapter
open NearCubicWires.InverseLengthStage
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.UniformTargetLanguageBank

theorem run_totalInverseSelectorSourceBank_fixedTarget
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
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
          (inverseScheduleLength contracts clockDepth advantageExponent target)
          target)
        (publishedSourceDrivenBankFuel
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent)
          (inverseLengthFuel contracts clockDepth advantageExponent
            ⟨target, fixedTargetCodeInput target⟩)
          (inverseScheduleLength contracts clockDepth advantageExponent target))
        (initialNPOracleState target target) =
      some
        (selectorDrivenBankFrame
          (publishedHierarchyOuterPCP contracts clockDepth)
          (publishedPointwisePCPP contracts)
          (inverseBankRate contracts advantageExponent)
          (inverseChainSourceIndex contracts clockDepth advantageExponent target)
          target) := by
  have hbank := run_inverseSelectorBank_closed contracts clockDepth
    advantageExponent target (fixedTargetCodeInput target)
  rw [encode_fixedTargetCodeInput] at hbank
  exact hbank

end NearCubicWires.TotalInverseSelectorAtomStreamSourceBank
