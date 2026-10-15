import Proof.Circuits.TotalInverseCanonicalLocalForwardBitsDomination

namespace NearCubicWires.TotalInverseCanonicalCompilerRequestFieldReduction

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.TotalInverseCanonicalCompilerRequestResources
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalLocalForwardBitsDomination
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

private abbrev Live
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) :=
  CanonicalCompilerLiveIndex contracts clockDepth machine advantageExponent pcp

private def liveMeasure
    {contracts : PublishedContracts} {clockDepth : ℕ}
    {machine : ExecutableWeakNondeterministicMachine}
    {advantageExponent : ℝ}
    {pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)}
    (request : Live contracts clockDepth machine advantageExponent pcp) : ℕ :=
  max 1 request.target

noncomputable def canonicalShapeCode
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) : ℕ :=
  pcp.shape.execute
    (inverseScheduleLength contracts clockDepth advantageExponent target)

noncomputable def canonicalScheduledWidth
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) : ℕ :=
  scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseSourceIndex
      (inverseSelectedSource contracts
        (publishedHierarchyOuterPCP contracts clockDepth)
        (inverseCoreAdvantagePower advantageExponent) target))

/-- The four true sources below the five request fields. -/
def CanonicalCompilerRequestSourcesDominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ) : Prop :=
  let Request := Live contracts clockDepth machine advantageExponent pcp
  let measureOf : Request → ℕ := liveMeasure
  Dominated
      (fun request : Request =>
        natBitLength
          (encodeTaggedList
            (canonicalOutputs contracts clockDepth machine advantageExponent
              pcp request.target)))
      measureOf degree ∧
    Dominated
      (fun request : Request =>
        canonicalShapeCode contracts clockDepth advantageExponent pcp
          request.target)
      measureOf degree ∧
    Dominated
      (fun request : Request =>
        canonicalScheduledWidth contracts clockDepth advantageExponent
          request.target)
      measureOf degree ∧
    Dominated
      (fun request : Request =>
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          request.target)
      measureOf degree

private theorem polyBounded_pow
    {value measure coefficient degree : ℕ}
    (hvalue : PolyBounded value measure coefficient degree)
    (exponent : ℕ) :
    PolyBounded (value ^ exponent) measure (coefficient ^ exponent)
      (degree * exponent) := by
  unfold PolyBounded at hvalue ⊢
  calc
    value ^ exponent ≤
        (coefficient * (measure + 1) ^ degree) ^ exponent :=
      Nat.pow_le_pow_left hvalue exponent
    _ = coefficient ^ exponent *
        (measure + 1) ^ (degree * exponent) := by
      rw [Nat.mul_pow, ← Nat.pow_mul]

private theorem canonicalWidth_le_shapeCode
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    canonicalWidth contracts clockDepth advantageExponent pcp target ≤
      canonicalShapeCode contracts clockDepth advantageExponent pcp target := by
  exact Nat.unpair_left_le _

private theorem canonicalCount_le_shapeCode
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (target : ℕ) :
    canonicalCount contracts clockDepth advantageExponent pcp target ≤
      canonicalShapeCode contracts clockDepth advantageExponent pcp target := by
  exact Nat.unpair_right_le _

private theorem canonicalBound_eq_oracleSizeBound
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (target : ℕ) :
    canonicalBound contracts clockDepth advantageExponent target =
      oracleSizeBound
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
        (canonicalScheduledWidth contracts clockDepth advantageExponent
          target) := by
  rfl

/-! The fixed pairing depth only multiplies the source degree. -/
theorem canonicalCompilerRequestFieldsDominated_of_sources
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hsources : CanonicalCompilerRequestSourcesDominated contracts clockDepth
      machine advantageExponent pcp degree) :
    CanonicalCompilerRequestFieldsDominated contracts clockDepth machine
      advantageExponent pcp
      (degree *
        2 ^ oracleDepth
          (inverseRequiredDegree contracts
            (inverseCoreAdvantagePower advantageExponent))) := by
  let Request := Live contracts clockDepth machine advantageExponent pcp
  let measureOf : Request → ℕ := liveMeasure
  let requiredDegree := inverseRequiredDegree contracts
    (inverseCoreAdvantagePower advantageExponent)
  let exponent := 2 ^ oracleDepth requiredDegree
  rcases hsources with ⟨htable, hshape, hscheduleWidth, hatomCount⟩
  change Dominated (fun request : Request =>
      natBitLength
        (encodeTaggedList
          (canonicalOutputs contracts clockDepth machine advantageExponent pcp
            request.target))) measureOf degree at htable
  change Dominated (fun request : Request =>
      canonicalShapeCode contracts clockDepth advantageExponent pcp
        request.target) measureOf degree at hshape
  change Dominated (fun request : Request =>
      canonicalScheduledWidth contracts clockDepth advantageExponent
        request.target) measureOf degree at hscheduleWidth
  change Dominated (fun request : Request =>
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        request.target) measureOf degree at hatomCount
  have hexponent : 1 ≤ exponent := by
    dsimp only [exponent]
    exact Nat.one_le_two_pow
  have hdegree : degree ≤ degree * exponent := by
    nlinarith
  have htable' := htable.degree_mono hdegree
  have hshape' := hshape.degree_mono hdegree
  have hwidth : Dominated (fun request : Request =>
      canonicalWidth contracts clockDepth advantageExponent pcp request.target)
      measureOf (degree * exponent) :=
    hshape'.mono fun request =>
      canonicalWidth_le_shapeCode contracts clockDepth advantageExponent pcp
        request.target
  have hcount : Dominated (fun request : Request =>
      canonicalCount contracts clockDepth advantageExponent pcp request.target)
      measureOf (degree * exponent) :=
    hshape'.mono fun request =>
      canonicalCount_le_shapeCode contracts clockDepth advantageExponent pcp
        request.target
  obtain ⟨widthCoefficient, hscheduleWidth⟩ := hscheduleWidth
  have hbound : Dominated (fun request : Request =>
      canonicalBound contracts clockDepth advantageExponent request.target)
      measureOf (degree * exponent) := by
    refine ⟨(widthCoefficient + 1) ^ exponent, fun request => ?_⟩
    change PolyBounded
      (canonicalBound contracts clockDepth advantageExponent request.target)
      (measureOf request) ((widthCoefficient + 1) ^ exponent)
      (degree * exponent)
    rw [canonicalBound_eq_oracleSizeBound]
    apply (polyBounded_pow
      ((hscheduleWidth request).add
        (polyBounded_const 1 (measureOf request) degree)) exponent).mono
    change pairIter (oracleDepth requiredDegree)
        (canonicalScheduledWidth contracts clockDepth advantageExponent
          request.target) ≤
      (canonicalScheduledWidth contracts clockDepth advantageExponent
          request.target + 1) ^ exponent
    calc
      pairIter (oracleDepth requiredDegree)
          (canonicalScheduledWidth contracts clockDepth advantageExponent
            request.target) ≤
          pairIter (oracleDepth requiredDegree)
              (canonicalScheduledWidth contracts clockDepth advantageExponent
                request.target) + 1 := Nat.le_succ _
      _ ≤ (canonicalScheduledWidth contracts clockDepth advantageExponent
              request.target + 1) ^ exponent := by
        simpa [exponent] using pairIter_add_one_le_pow
          (oracleDepth requiredDegree)
          (canonicalScheduledWidth contracts clockDepth advantageExponent
            request.target)
  exact ⟨htable', hwidth, hcount, hbound,
    hatomCount.degree_mono hdegree⟩

end NearCubicWires.TotalInverseCanonicalCompilerRequestFieldReduction
