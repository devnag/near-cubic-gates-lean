import Proof.PCP.PaddedProjectionQueryRunner

namespace NearCubicWires.PaddedProjectionPresentedPCP

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionDecisionRunner
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedProjectionQueryRunner
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionShapeRunner
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces

/-! ## 1. The single residual statement -/

/-- **The padded runners' budget.**  The three published streams' widths and
clocks are dominated by one declared polynomial budget at each runner's own
charged measure.  Nothing else about the runners is left open: their outputs
are already fixed by the three execution theorems of the runner modules. -/
def PaddedRunnerBudget {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (coefficient degree : ℕ) : Prop :=
  0 < coefficient ∧
  (∀ n,
    publishedPaddedShapeBits outer n ≤
      polynomialBudget coefficient degree (shapeMeasure clockDepth n)) ∧
  (∀ n,
    publishedPaddedShapeFuel outer n ≤
      polynomialBudget coefficient degree (shapeMeasure clockDepth n)) ∧
  (∀ n,
    natBitLength n ≤
      polynomialBudget coefficient degree (shapeMeasure clockDepth n)) ∧
  (∀ request,
    publishedPaddedQueryBits outer request ≤
      polynomialBudget coefficient degree
        (ProjectionQueryRequest.measure request)) ∧
  (∀ request,
    publishedPaddedQueryFuel outer request ≤
      polynomialBudget coefficient degree
        (ProjectionQueryRequest.measure request)) ∧
  (∀ request,
    natBitLength
        (max (ProjectionQueryRequest.length request)
          (ProjectionQueryRequest.code request)) ≤
      polynomialBudget coefficient degree
        (ProjectionQueryRequest.measure request)) ∧
  (∀ request,
    publishedPaddedDecisionBits outer request ≤
      polynomialBudget coefficient degree
        (ProjectionDecisionRequest.measure request)) ∧
  (∀ request,
    publishedPaddedDecisionFuel outer request ≤
      polynomialBudget coefficient degree
        (ProjectionDecisionRequest.measure request)) ∧
  (∀ request,
    natBitLength
        (max (ProjectionDecisionRequest.length request)
          (ProjectionDecisionRequest.code request)) ≤
      polynomialBudget coefficient degree
        (ProjectionDecisionRequest.measure request))

/-! ## 2. The presented PCP -/

/-- **The padded presentation is inhabited.**  One polynomial budget for the
three published streams inhabits `PresentsPaddedOuterPCP`, and hence discharges
the residual premise of
`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation`. -/
theorem exists_presentsPaddedOuterPCP {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (coefficient degree : ℕ)
    (hbudget : PaddedRunnerBudget outer coefficient degree) :
    ∃ pcp :
        ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth),
      PresentsPaddedOuterPCP outer pcp := by
  obtain ⟨hcoefficient, hshapeBits, hshapeFuel, hshapeInitial, hqueryBits,
    hqueryFuel, hqueryInitial, hdecisionBits, hdecisionFuel,
    hdecisionInitial⟩ := hbudget
  exact
    ⟨_,
      presentsPaddedOuterPCP_paddedExecutablePCP outer
        (publishedPaddedShapeProgram outer) (publishedPaddedQueryProgram outer)
        (publishedPaddedDecisionProgram outer)
        (publishedPaddedShapeProgram_oracleFree outer)
        (publishedPaddedQueryProgram_oracleFree outer)
        (publishedPaddedDecisionProgram_oracleFree outer) coefficient degree
        hcoefficient (publishedPaddedShapeBits outer)
        (publishedPaddedShapeFuel outer) (publishedPaddedQueryBits outer)
        (publishedPaddedQueryFuel outer) (publishedPaddedDecisionBits outer)
        (publishedPaddedDecisionFuel outer) hshapeBits hshapeFuel hshapeInitial
        (run_publishedPaddedShapeProgram outer) hqueryBits hqueryFuel
        hqueryInitial (run_publishedPaddedQueryProgram outer) hdecisionBits
        hdecisionFuel hdecisionInitial
        (run_publishedPaddedDecisionProgram outer)⟩

theorem inverse_bodyRun_of_runnerBudget (contracts : PublishedContracts)
    (clockDepth : ℕ) (coefficient degree : ℕ)
    (hbudget :
      PaddedRunnerBudget (publishedHierarchyOuterPCP contracts clockDepth)
        coefficient degree) :
    ∃ pcp :
        ExecutableProjectionPCP
          (publishedRefuterSource contracts clockDepth).hierarchyMachine
          (pairClock clockDepth),
      PresentsPaddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth)
        pcp :=
  exists_presentsPaddedOuterPCP
    (publishedHierarchyOuterPCP contracts clockDepth) coefficient degree
    hbudget

end NearCubicWires.PaddedProjectionPresentedPCP
