import Proof.Circuits.TotalInverseCanonicalCompiledBodyResources

namespace NearCubicWires.TotalInverseCanonicalBodySelectorResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorCanonicalResourceFrontier
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenBodyDispatch
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseCanonicalCompiledBodyResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseCanonicalRangeResources
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

private abbrev Request := LanguageEvaluationRequest
private def measureOf (request : Request) : ℕ := request.measure

noncomputable def canonicalBodyEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) (request : Request) : ℕ :=
  totalInverseSelectorBankEmitterBits contracts clockDepth machine
    advantageExponent pcp
    (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerBits contracts clockDepth machine
        advantageExponent pcp))
    (totalInverseCanonicalRangeBits contracts clockDepth machine
      advantageExponent pcp) request

noncomputable def canonicalBodyQueryBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  recoveryQuerySelectorBits
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent request.length)
    request.length
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent request)

noncomputable def canonicalBodyEmitterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) (request : Request) : ℕ :=
  totalInverseBankEmitterFuel contracts clockDepth machine advantageExponent pcp
    (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerFuel contracts clockDepth machine
        advantageExponent pcp))
    (totalInverseCanonicalCompilerFuel contracts clockDepth machine
      advantageExponent pcp) request

noncomputable def canonicalBodyQueryFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  recoveryQuerySelectorFuel
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent request.length)

def CanonicalBodySelectorLocalFrontierDominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) (degree : ℕ) : Prop :=
  Dominated
      (totalInverseCanonicalCompiledBodyPointBits contracts clockDepth
        advantageExponent) measureOf degree ∧
    Dominated
      (canonicalBodyEmitterBits contracts clockDepth machine advantageExponent
        pcp) measureOf degree ∧
    Dominated
      (canonicalBodyQueryBits contracts clockDepth machine advantageExponent)
      measureOf degree ∧
    Dominated
      (canonicalBodyEmitterFuel contracts clockDepth machine advantageExponent
        pcp) measureOf degree ∧
    Dominated
      (canonicalBodyQueryFuel contracts clockDepth machine advantageExponent)
      measureOf degree

set_option maxHeartbeats 800000 in
-- The exact selector expansion normalizes the full canonical range pipeline.
theorem canonicalCompiledBodySelectorFrontier_dominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) (degree : ℕ) (hdegree : 1 ≤ degree)
    (hlocal : CanonicalBodySelectorLocalFrontierDominated contracts clockDepth
      machine advantageExponent pcp degree) :
    Dominated
        (totalInverseCanonicalCompiledBodyPointBits contracts clockDepth
          advantageExponent) measureOf degree ∧
      Dominated
        (totalInverseCanonicalCompiledBodySelectorBits contracts clockDepth
          machine advantageExponent pcp) measureOf degree ∧
      Dominated
        (totalInverseCanonicalCompiledBodySelectorFuel contracts clockDepth
          machine advantageExponent pcp) measureOf degree := by
  rcases hlocal with ⟨hpoint, hemitsBits, hqueryBits, hemitsFuel, hqueryFuel⟩
  have hlength : Dominated (fun request : Request => natBitLength request.length)
      measureOf degree :=
    ⟨1, fun request =>
      (requestLengthBits_polyBounded request).degree_mono hdegree⟩
  have hselectorBits := hlength.max (hemitsBits.max hqueryBits)
  obtain ⟨emitsFuelCoefficient, hemitsFuel⟩ := hemitsFuel
  obtain ⟨queryFuelCoefficient, hqueryFuel⟩ := hqueryFuel
  let fuelCoefficient := programRegisterSpan recoveryQuerySelectorProgram + 5 +
    emitsFuelCoefficient + queryFuelCoefficient
  have hselectorFuel : Dominated
      (totalInverseCanonicalCompiledBodySelectorFuel contracts clockDepth
        machine advantageExponent pcp) measureOf degree := by
    refine ⟨fuelCoefficient, fun request => ?_⟩
    simpa only [totalInverseCanonicalCompiledBodySelectorFuel,
      canonicalBodyEmitterFuel, canonicalBodyQueryFuel,
      inverseBankSelectorFuel, emittedBranchSelectorFuel,
      inverseScheduleBound] using
      (linkFuel_polyBounded (second := recoveryQuerySelectorProgram)
        (hemitsFuel request) (hqueryFuel request)).coefficient_mono (by
          dsimp only [fuelCoefficient]
          omega)
  refine ⟨hpoint, ?_, hselectorFuel⟩
  change Dominated
    (fun request : Request =>
      max (natBitLength request.length)
        (max
          (canonicalBodyEmitterBits contracts clockDepth machine
            advantageExponent pcp request)
          (canonicalBodyQueryBits contracts clockDepth machine
            advantageExponent request))) measureOf degree
  exact hselectorBits

end NearCubicWires.TotalInverseCanonicalBodySelectorResources
