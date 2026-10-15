import Proof.Circuits.TotalSelectorDrivenShapeTail

/-! # All-request guarded selector atom-shape run -/

namespace NearCubicWires.TotalSelectorDrivenShapeRuns

open NearCubicWires
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalSelectorAtomShapeProgram
open NearCubicWires.TotalSelectorDrivenContextContracts
open NearCubicWires.TotalSelectorDrivenShapeTail

/-- The guarded atom-count tail is total at the selector frame once its
context is total.  Positivity is used only for the structural formula's atom
count, never for the external request length. -/
theorem totalInverseSelectorAtomShapeRuns_ofTotalContext
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine) (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (context : NPOracleProgram)
    (contextBits contextFuel : LanguageEvaluationRequest → ℕ)
    (compilerBits compilerFuel : ℕ → ℕ → ℕ)
    (hcontext :
      TotalInverseSelectorAtomContextRuns contracts clockDepth machine
        advantageExponent pcp context contextBits contextFuel)
    (hcompiler :
      TotalInverseCompilerRuns contracts clockDepth machine advantageExponent
        pcp compilerBits compilerFuel) :
    TotalInverseSelectorAtomShapeRuns contracts clockDepth machine
      advantageExponent pcp (totalInverseAtomShapeProgram context)
      (inverseAtomShapeBits contracts clockDepth machine advantageExponent pcp
        contextBits compilerBits)
      (totalInverseAtomShapeFuel contracts clockDepth machine advantageExponent
        pcp contextFuel compilerFuel) := by
  intro request
  exact run_occurrenceStage (hcontext request)
    (run_totalInverseSelectorAtomShapeTail contracts clockDepth machine
      advantageExponent pcp compilerBits compilerFuel hcompiler request)

end NearCubicWires.TotalSelectorDrivenShapeRuns
