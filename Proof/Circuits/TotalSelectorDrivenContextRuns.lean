import Proof.Circuits.TotalSelectorDrivenContextPipeline

/-! # All-request selector atom-context run -/

namespace NearCubicWires.TotalSelectorDrivenContextRuns

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContext
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.TotalSelectorDrivenAdapterContracts
open NearCubicWires.TotalSelectorDrivenContextContracts
open NearCubicWires.TotalSelectorDrivenContextPipeline

/-- The selector atom-context composition is total once its table call is
total.  The proof is the frozen register pipeline with its former onset
argument deleted. -/
theorem totalInverseSelectorAtomContextRuns_ofTable
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp)
    (table : NPOracleProgram)
    (tableBits tableFuel : LanguageEvaluationRequest → ℕ)
    (htable :
      TotalInverseSelectorAtomTableRuns contracts clockDepth machine
        advantageExponent pcp table tableBits tableFuel) :
    TotalInverseSelectorAtomContextRuns contracts clockDepth machine
      advantageExponent pcp
      (inverseAtomContextProgram
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        table)
      (inverseSelectorAtomContextBits contracts clockDepth machine
        advantageExponent pcp tableBits)
      (inverseAtomContextFuel contracts advantageExponent table tableFuel) := by
  intro request
  refine Eq.trans ?_
    (congrArg some
      (inverseAtomContext_ofSelectorRegisters contracts clockDepth machine
        advantageExponent pcp hpresentation request.length))
  exact run_totalInverseSelectorAtomContextProgram_ofTable contracts clockDepth
    machine advantageExponent pcp table tableBits tableFuel htable request

end NearCubicWires.TotalSelectorDrivenContextRuns
