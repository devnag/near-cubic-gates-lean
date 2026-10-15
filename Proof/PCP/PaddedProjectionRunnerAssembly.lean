import Proof.MachineModel.ExecutableRecoveryMachine
import Proof.PCP.PaddedProjectionRunnerOutputs

namespace NearCubicWires.PaddedProjectionRunnerAssembly

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The two request-level outputs -/

/-- The padded query output, read off the query request record. -/
def paddedQueryRequestOutput {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (request : ProjectionQueryRequest) : ℕ :=
  paddedQueryOutput outer request.inputArity (encodeBitInput request.input)
    request.query.val request.bit.val

/-- The padded decision output, read off the decision request record. -/
def paddedDecisionRequestOutput {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source) (request : ProjectionDecisionRequest) :
    ℕ :=
  paddedDecisionOutput outer request.inputArity (encodeBitInput request.input)
    (encodeBitInput request.randomness)

/-- **The presentation, from three runner-level equalities.**  Each hypothesis
is quantified over the runner's own request type, which is the shape a
`polynomialNatProgramOfRun` correctness theorem produces. -/
theorem presentsPaddedOuterPCP_of_runners {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (pcp :
      ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth))
    (hshape : ∀ n, pcp.shape.execute n = paddedShapeOutput outer n)
    (hquery : ∀ request,
      pcp.query.execute request = paddedQueryRequestOutput outer request)
    (hdecision : ∀ request,
      pcp.decisionRunner.execute request =
        paddedDecisionRequestOutput outer request) :
    PresentsPaddedOuterPCP outer pcp :=
  presentsPaddedOuterPCP_of_executes outer pcp hshape
    (fun _ input query bit => hquery (pcp.queryRequest input query bit))
    (fun _ input randomness => hdecision (pcp.decisionRequest input randomness))

/-! ## 2. The record -/

/-- The padded presentation's own charged measure on the shape request. -/
def shapeMeasure (clockDepth n : ℕ) : ℕ :=
  n + logScale (pairClock clockDepth n)

/-- **The padded executable projection PCP.**  Three fixed instruction streams,
three named charges, three exact runs. -/
def paddedExecutablePCP {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (shapeProgram queryProgram decisionProgram : NPOracleProgram)
    (hshapeOracleFree : OracleFree shapeProgram)
    (hqueryOracleFree : OracleFree queryProgram)
    (hdecisionOracleFree : OracleFree decisionProgram)
    (coefficient degree : ℕ) (hcoefficient : 0 < coefficient)
    (shapeBits shapeFuel : ℕ → ℕ)
    (queryBits queryFuel : ProjectionQueryRequest → ℕ)
    (decisionBits decisionFuel : ProjectionDecisionRequest → ℕ)
    (hshapeBits : ∀ n,
      shapeBits n ≤ polynomialBudget coefficient degree (shapeMeasure clockDepth n))
    (hshapeFuel : ∀ n,
      shapeFuel n ≤ polynomialBudget coefficient degree (shapeMeasure clockDepth n))
    (hshapeInitial : ∀ n,
      natBitLength n ≤
        polynomialBudget coefficient degree (shapeMeasure clockDepth n))
    (hshapeRun : ∀ n,
      runNPOracleProgram shapeProgram (shapeBits n) (shapeFuel n)
          (initialNPOracleState n n) =
        some (paddedShapeOutput outer n))
    (hqueryBits : ∀ request,
      queryBits request ≤
        polynomialBudget coefficient degree
          (ProjectionQueryRequest.measure request))
    (hqueryFuel : ∀ request,
      queryFuel request ≤
        polynomialBudget coefficient degree
          (ProjectionQueryRequest.measure request))
    (hqueryInitial : ∀ request,
      natBitLength
          (max (ProjectionQueryRequest.length request)
            (ProjectionQueryRequest.code request)) ≤
        polynomialBudget coefficient degree
          (ProjectionQueryRequest.measure request))
    (hqueryRun : ∀ request,
      runNPOracleProgram queryProgram (queryBits request) (queryFuel request)
          (initialNPOracleState (ProjectionQueryRequest.length request)
            (ProjectionQueryRequest.code request)) =
        some (paddedQueryRequestOutput outer request))
    (hdecisionBits : ∀ request,
      decisionBits request ≤
        polynomialBudget coefficient degree
          (ProjectionDecisionRequest.measure request))
    (hdecisionFuel : ∀ request,
      decisionFuel request ≤
        polynomialBudget coefficient degree
          (ProjectionDecisionRequest.measure request))
    (hdecisionInitial : ∀ request,
      natBitLength
          (max (ProjectionDecisionRequest.length request)
            (ProjectionDecisionRequest.code request)) ≤
        polynomialBudget coefficient degree
          (ProjectionDecisionRequest.measure request))
    (hdecisionRun : ∀ request,
      runNPOracleProgram decisionProgram (decisionBits request)
          (decisionFuel request)
          (initialNPOracleState (ProjectionDecisionRequest.length request)
            (ProjectionDecisionRequest.code request)) =
        some (paddedDecisionRequestOutput outer request)) :
    ExecutableProjectionPCP source.hierarchyMachine (pairClock clockDepth) where
  shape :=
    polynomialNatProgramOfRun (inputLength := id) (requestCode := id)
      (measure := shapeMeasure clockDepth) shapeProgram coefficient degree
      hcoefficient shapeBits shapeFuel (paddedShapeOutput outer) hshapeBits
      hshapeFuel (fun n => by simpa using hshapeInitial n) hshapeRun
  shapeOracleFree := hshapeOracleFree
  query :=
    polynomialNatProgramOfRun (inputLength := ProjectionQueryRequest.length)
      (requestCode := ProjectionQueryRequest.code)
      (measure := ProjectionQueryRequest.measure) queryProgram coefficient
      degree hcoefficient queryBits queryFuel (paddedQueryRequestOutput outer)
      hqueryBits hqueryFuel hqueryInitial hqueryRun
  queryOracleFree := hqueryOracleFree
  decisionRunner :=
    polynomialNatProgramOfRun (inputLength := ProjectionDecisionRequest.length)
      (requestCode := ProjectionDecisionRequest.code)
      (measure := ProjectionDecisionRequest.measure) decisionProgram
      coefficient degree hcoefficient decisionBits decisionFuel
      (paddedDecisionRequestOutput outer) hdecisionBits hdecisionFuel
      hdecisionInitial hdecisionRun
  decisionOracleFree := hdecisionOracleFree

/-- **The padded presentation, executed.**  Nine explicit facts about three
oracle-free instruction streams inhabit `PresentsPaddedOuterPCP`. -/
theorem presentsPaddedOuterPCP_paddedExecutablePCP {clockDepth : ℕ}
    {source : ExecutableRefuterSource (pairClock clockDepth)}
    (outer : HierarchyOuterPCP source)
    (shapeProgram queryProgram decisionProgram : NPOracleProgram)
    (hshapeOracleFree : OracleFree shapeProgram)
    (hqueryOracleFree : OracleFree queryProgram)
    (hdecisionOracleFree : OracleFree decisionProgram)
    (coefficient degree : ℕ) (hcoefficient : 0 < coefficient)
    (shapeBits shapeFuel : ℕ → ℕ)
    (queryBits queryFuel : ProjectionQueryRequest → ℕ)
    (decisionBits decisionFuel : ProjectionDecisionRequest → ℕ)
    (hshapeBits : ∀ n,
      shapeBits n ≤ polynomialBudget coefficient degree (shapeMeasure clockDepth n))
    (hshapeFuel : ∀ n,
      shapeFuel n ≤ polynomialBudget coefficient degree (shapeMeasure clockDepth n))
    (hshapeInitial : ∀ n,
      natBitLength n ≤
        polynomialBudget coefficient degree (shapeMeasure clockDepth n))
    (hshapeRun : ∀ n,
      runNPOracleProgram shapeProgram (shapeBits n) (shapeFuel n)
          (initialNPOracleState n n) =
        some (paddedShapeOutput outer n))
    (hqueryBits : ∀ request,
      queryBits request ≤
        polynomialBudget coefficient degree
          (ProjectionQueryRequest.measure request))
    (hqueryFuel : ∀ request,
      queryFuel request ≤
        polynomialBudget coefficient degree
          (ProjectionQueryRequest.measure request))
    (hqueryInitial : ∀ request,
      natBitLength
          (max (ProjectionQueryRequest.length request)
            (ProjectionQueryRequest.code request)) ≤
        polynomialBudget coefficient degree
          (ProjectionQueryRequest.measure request))
    (hqueryRun : ∀ request,
      runNPOracleProgram queryProgram (queryBits request) (queryFuel request)
          (initialNPOracleState (ProjectionQueryRequest.length request)
            (ProjectionQueryRequest.code request)) =
        some (paddedQueryRequestOutput outer request))
    (hdecisionBits : ∀ request,
      decisionBits request ≤
        polynomialBudget coefficient degree
          (ProjectionDecisionRequest.measure request))
    (hdecisionFuel : ∀ request,
      decisionFuel request ≤
        polynomialBudget coefficient degree
          (ProjectionDecisionRequest.measure request))
    (hdecisionInitial : ∀ request,
      natBitLength
          (max (ProjectionDecisionRequest.length request)
            (ProjectionDecisionRequest.code request)) ≤
        polynomialBudget coefficient degree
          (ProjectionDecisionRequest.measure request))
    (hdecisionRun : ∀ request,
      runNPOracleProgram decisionProgram (decisionBits request)
          (decisionFuel request)
          (initialNPOracleState (ProjectionDecisionRequest.length request)
            (ProjectionDecisionRequest.code request)) =
        some (paddedDecisionRequestOutput outer request)) :
    PresentsPaddedOuterPCP outer
      (paddedExecutablePCP outer shapeProgram queryProgram decisionProgram
        hshapeOracleFree hqueryOracleFree hdecisionOracleFree coefficient degree
        hcoefficient shapeBits shapeFuel queryBits queryFuel decisionBits
        decisionFuel hshapeBits hshapeFuel hshapeInitial hshapeRun hqueryBits
        hqueryFuel hqueryInitial hqueryRun hdecisionBits hdecisionFuel
        hdecisionInitial hdecisionRun) := by
  refine presentsPaddedOuterPCP_of_runners outer _ ?_ ?_ ?_
  · intro n
    exact polynomialNatProgramOfRun_execute (inputLength := id)
      (requestCode := id) (measure := shapeMeasure clockDepth) shapeProgram
      coefficient degree hcoefficient shapeBits shapeFuel
      (paddedShapeOutput outer) hshapeBits hshapeFuel
      (fun n => by simpa using hshapeInitial n) hshapeRun n
  · intro request
    exact polynomialNatProgramOfRun_execute
      (inputLength := ProjectionQueryRequest.length)
      (requestCode := ProjectionQueryRequest.code)
      (measure := ProjectionQueryRequest.measure) queryProgram coefficient
      degree hcoefficient queryBits queryFuel (paddedQueryRequestOutput outer)
      hqueryBits hqueryFuel hqueryInitial hqueryRun request
  · intro request
    exact polynomialNatProgramOfRun_execute
      (inputLength := ProjectionDecisionRequest.length)
      (requestCode := ProjectionDecisionRequest.code)
      (measure := ProjectionDecisionRequest.measure) decisionProgram
      coefficient degree hcoefficient decisionBits decisionFuel
      (paddedDecisionRequestOutput outer) hdecisionBits hdecisionFuel
      hdecisionInitial hdecisionRun request

end NearCubicWires.PaddedProjectionRunnerAssembly
