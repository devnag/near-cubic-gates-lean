import Proof.Circuits.TotalSelectorDrivenFrameRuns
import Proof.Circuits.TotalSelectorDrivenAdapterRuns
import Proof.Circuits.TotalSelectorBodyAdapter

/-! # Concrete all-request guarded selector body adapter -/

namespace NearCubicWires.TotalSelectorDrivenBodyAdapterRuns

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenProjectionTableStage
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenAdapterRuns
open NearCubicWires.TotalSelectorDrivenContextContracts
open NearCubicWires.TotalSelectorDrivenContextRuns
open NearCubicWires.TotalSelectorDrivenFrameRuns
open NearCubicWires.TotalSelectorDrivenShapeRuns

set_option maxHeartbeats 1600000 in
-- The concrete selector-frame resources contain the scheduled-index scan.
/-- Presentation, the total compiler, and the concrete projection-table stage
supply the guarded body adapter for every selector request. -/
theorem totalInverseSelectorBodyAdapterTotalRuns
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
    TotalInverseSelectorFrameAdapterRuns contracts clockDepth machine
      advantageExponent pcp
      (totalInverseSelectorBodyAdapterProgram contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp compilerBits)
      (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp compilerFuel) :=
  totalInverseSelectorFrameAdapterRuns_ofShape contracts clockDepth machine
    advantageExponent pcp
    (totalInverseSelectorBodyShapeProgram contracts clockDepth machine
      advantageExponent pcp)
    (totalInverseSelectorBodyShapeBits contracts clockDepth machine
      advantageExponent pcp compilerBits)
    (totalInverseSelectorBodyShapeFuel contracts clockDepth machine
      advantageExponent pcp compilerFuel)
    (totalInverseSelectorAtomShapeRuns_ofTotalContext contracts clockDepth
      machine advantageExponent pcp
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
      (totalInverseSelectorAtomContextRuns_ofTable contracts clockDepth machine
        advantageExponent pcp hpresentation
        (inverseSelectorBankTableProgram contracts clockDepth machine pcp)
        (inverseSelectorBankTableBits contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
        (inverseSelectorBankTableFuel contracts clockDepth machine
          advantageExponent pcp
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent))
        (totalInverseSelectorAtomTableRuns_ofPresentation contracts clockDepth
          machine advantageExponent pcp hpresentation))
      hcompiler)

end NearCubicWires.TotalSelectorDrivenBodyAdapterRuns
