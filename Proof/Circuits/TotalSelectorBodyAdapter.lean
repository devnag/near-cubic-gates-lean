import Proof.Circuits.SelectorDrivenBodyClosure
import Proof.MachineModel.TotalSelectorAtomShapeProgram

/-!
# The guarded selector-frame body adapter

This replaces only the selector adapter's atom-count shape tail.  Projection
table/context construction and the retained-frame ABI remain unchanged.
-/

namespace NearCubicWires.TotalSelectorBodyAdapter

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyClosure
open NearCubicWires.SelectorDrivenProjectionPresentation
open NearCubicWires.SelectorDrivenProjectionTableStage
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectorAtomShapeProgram

noncomputable def totalInverseSelectorBodyShapeProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  totalInverseAtomShapeProgram
    (inverseAtomContextProgram
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
      (inverseSelectorBankTableProgram contracts clockDepth machine pcp))

noncomputable def totalInverseSelectorBodyShapeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseAtomShapeBits contracts clockDepth machine advantageExponent pcp
    (inverseSelectorAtomContextBits contracts clockDepth machine
      advantageExponent pcp
      (inverseSelectorBankTableBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
    compilerBits

noncomputable def totalInverseSelectorBodyShapeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  totalInverseAtomShapeFuel contracts clockDepth machine advantageExponent pcp
    (inverseAtomContextFuel contracts advantageExponent
      (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
      (inverseSelectorBankTableFuel contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
    compilerFuel

noncomputable def totalInverseSelectorBodyAdapterProgram
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) : NPOracleProgram :=
  inverseFrameAdapterProgram
    (totalInverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)

noncomputable def totalInverseSelectorBodyAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerBits : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseSelectorFrameAdapterBits contracts clockDepth machine
    advantageExponent pcp
    (totalInverseSelectorBodyShapeBits contracts clockDepth machine
      advantageExponent pcp compilerBits)

noncomputable def totalInverseSelectorBodyAdapterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (compilerFuel : ℕ → ℕ → ℕ) : LanguageEvaluationRequest → ℕ :=
  inverseFrameAdapterFuel
    (totalInverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseSelectorBodyShapeFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)

set_option maxHeartbeats 1600000 in
-- The selector-frame functions contain the noncomputable scheduled index.
theorem totalInverseSelectorBodyAdapterRuns
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcompiler :
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel) :
    InverseSelectorFrameAdapterRuns contracts clockDepth machine
      advantageExponent pcp
      (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits)
      (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) :=
  inverseSelectorFrameAdapterRuns_ofShape contracts clockDepth machine
    advantageExponent pcp
    (totalInverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseSelectorBodyShapeBits contracts clockDepth machine
      advantageExponent pcp compilerBits)
    (totalInverseSelectorBodyShapeFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    (totalInverseSelectorAtomShapeRuns_ofContext contracts clockDepth machine
      advantageExponent pcp
      (inverseAtomContextProgram
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp))
      (inverseSelectorAtomContextBits contracts clockDepth machine
        advantageExponent pcp
        (inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
      (inverseAtomContextFuel contracts advantageExponent
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)))
      compilerBits compilerFuel
      (inverseSelectorAtomContextRuns_ofTable contracts clockDepth machine
        advantageExponent pcp hpresentation
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
        (inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
        (inverseSelectorAtomTableRuns_ofPresentation contracts clockDepth machine
          advantageExponent pcp hpresentation))
      hcompiler)

end NearCubicWires.TotalSelectorBodyAdapter
