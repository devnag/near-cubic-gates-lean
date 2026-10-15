import Proof.Circuits.SelectorDrivenEmitterRuns
import Proof.MachineModel.TotalStructuralAtomEmitterProgram

/-!
# Guarded selector-frame emitter resources

This module freezes the width ledger for the total structural atom emitter at
the selector-driven frame. Program and fuel ownership remain in the already
frozen total bank-emitter definitions.
-/

namespace NearCubicWires.TotalSelectorDrivenEmitterResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.TotalStructuralAtomEmitterProgram

noncomputable def totalInverseSelectorBankEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (adapterBits : LanguageEvaluationRequest → ℕ) (rangeBits : ℕ → ℕ)
    (request : LanguageEvaluationRequest) : ℕ :=
  occurrenceStageBits (LanguageEvaluationRequest.length request)
    (adapterBits request)
    (totalStructuralAtomEmitterBits
      (rangeBits (LanguageEvaluationRequest.length request))
      (LanguageEvaluationRequest.length request)
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        (LanguageEvaluationRequest.length request))
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent (LanguageEvaluationRequest.length request)))

end NearCubicWires.TotalSelectorDrivenEmitterResources
