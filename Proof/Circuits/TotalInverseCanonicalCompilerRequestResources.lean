import Proof.Circuits.PaddedRunnerBudgetDomination
import Proof.Circuits.TotalInverseCanonicalCompilerResources
import Proof.Circuits.ValidatorCompositeLeafBounds

/-! # Polynomial width of the canonical inverse compiler request

The compiler request is an eight-field nested pairing.  This module closes
that pairing layer from the five exact magnitude facts that occur below it:
the tagged projection-output table, native width, query count, oracle bound,
and compiled formula length.  No execution theorem is used to infer any of
those magnitudes.
-/

namespace NearCubicWires.TotalInverseCanonicalCompilerRequestResources

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

/-! ## 1. The exact live-index domain -/

/-- One compiler request that is actually consumed by the inverse atom loop. -/
structure CanonicalCompilerLiveIndex
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth)) where
  target : ℕ
  index : ℕ
  isLt :
    index <
      inverseAtomCount contracts clockDepth machine advantageExponent pcp target

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

/-! ## 2. The five exact lower magnitudes -/

def CanonicalCompilerRequestFieldsDominated
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
        canonicalWidth contracts clockDepth advantageExponent pcp
          request.target)
      measureOf degree ∧
    Dominated
      (fun request : Request =>
        canonicalCount contracts clockDepth advantageExponent pcp
          request.target)
      measureOf degree ∧
    Dominated
      (fun request : Request =>
        canonicalBound contracts clockDepth advantageExponent request.target)
      measureOf degree ∧
    Dominated
      (fun request : Request =>
        inverseAtomCount contracts clockDepth machine advantageExponent pcp
          request.target)
      measureOf degree

private theorem dominated_natBitLength_of_value
    {Request : Type} {value measureOf : Request → ℕ} {degree : ℕ}
    (hvalue : Dominated value measureOf degree) :
    Dominated (fun request => natBitLength (value request)) measureOf degree := by
  obtain ⟨coefficient, hvalue⟩ := hvalue
  exact ⟨coefficient + 1, fun request =>
    polyBounded_natBitLength_of_polyBounded (hvalue request)⟩

/-! ## 3. Close the eight-field ABI pairing -/

/-- The exact canonical request-code head is polynomial once its five actual
lower magnitudes are.  Pairing preserves degree; only the product inside
`descriptionWidth` doubles it.
-/
theorem totalInverseCanonicalCompilerRequestBits_dominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ)
    (hfields : CanonicalCompilerRequestFieldsDominated contracts clockDepth
      machine advantageExponent pcp degree) :
    ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerRequestBits contracts clockDepth machine
          advantageExponent pcp)
        coefficient (degree + degree) := by
  let Request := Live contracts clockDepth machine advantageExponent pcp
  let measureOf : Request → ℕ := liveMeasure
  let outputs : Request → List ℕ := fun request =>
    canonicalOutputs contracts clockDepth machine advantageExponent pcp
      request.target
  let width : Request → ℕ := fun request =>
    canonicalWidth contracts clockDepth advantageExponent pcp request.target
  let count : Request → ℕ := fun request =>
    canonicalCount contracts clockDepth advantageExponent pcp request.target
  let bound : Request → ℕ := fun request =>
    canonicalBound contracts clockDepth advantageExponent request.target
  rcases hfields with ⟨htable, hwidth, hcount, hbound, hatomCount⟩
  change Dominated (fun request : Request =>
      natBitLength (encodeTaggedList (outputs request))) measureOf degree at htable
  change Dominated width measureOf degree at hwidth
  change Dominated count measureOf degree at hcount
  change Dominated bound measureOf degree at hbound
  change Dominated (fun request : Request =>
      inverseAtomCount contracts clockDepth machine advantageExponent pcp
        request.target) measureOf degree at hatomCount
  have hindex : Dominated (fun request : Request => request.index)
      measureOf degree :=
    hatomCount.mono fun request => Nat.le_of_lt request.isLt
  have hone : Dominated (fun _ : Request => 1) measureOf degree :=
    dominated_const 1 degree
  have hsix : Dominated (fun _ : Request => 6) measureOf degree :=
    dominated_const 6 degree
  have hfieldLimit :
      Dominated (fun request : Request =>
        width request + bound request + 1) measureOf degree :=
    (hwidth.add hbound).add hone
  have hrowWidth :
      Dominated (fun request : Request =>
        6 + 2 * (width request + bound request + 1)) measureOf degree :=
    hsix.add (hfieldLimit.const_mul 2)
  have hboundSucc :
      Dominated (fun request : Request => bound request + 1)
        measureOf degree :=
    hbound.add hone
  have hinputArityRaw :
      Dominated (fun request : Request =>
        (bound request + 1) *
          (6 + 2 * (width request + bound request + 1)))
        measureOf (degree + degree) :=
    hboundSucc.mul hrowWidth
  have hinputArity :
      Dominated (fun request : Request =>
        structuralInputArity (width request) (bound request))
        measureOf (degree + degree) := by
    simpa [structuralInputArity, descriptionWidth,
      boundedCircuitDescriptionWidth, boundedCircuitFieldLimit] using
      hinputArityRaw
  have htarget :
      Dominated (fun request : Request =>
        request.index - structuralInputArity (width request) (bound request))
        measureOf degree :=
    hindex.mono fun request => Nat.sub_le _ _
  have hzeroBits :
      Dominated (fun _ : Request => natBitLength 0) measureOf degree :=
    dominated_const (natBitLength 0) degree
  have htargetBits := dominated_natBitLength_of_value htarget
  have hstateBits :
      Dominated (fun request : Request =>
        natBitLength
          (selectiveEmitStateCode
            (request.index -
              structuralInputArity (width request) (bound request)) 0 0))
        measureOf degree := by
    simpa [selectiveEmitStateCode] using
      htargetBits.natBitLength_pair
        (hzeroBits.natBitLength_pair hzeroBits)
  have hwidthBits := dominated_natBitLength_of_value hwidth
  have hcountBits := dominated_natBitLength_of_value hcount
  have hboundBits := dominated_natBitLength_of_value hbound
  have hfieldLimitBits := dominated_natBitLength_of_value hfieldLimit
  have hrowWidthBits := dominated_natBitLength_of_value hrowWidth
  have hinputArityBits := dominated_natBitLength_of_value hinputArity
  have hdegree : degree ≤ degree + degree := by omega
  have hstateBits' := hstateBits.degree_mono hdegree
  have htable' := htable.degree_mono hdegree
  have hwidthBits' := hwidthBits.degree_mono hdegree
  have hcountBits' := hcountBits.degree_mono hdegree
  have hboundBits' := hboundBits.degree_mono hdegree
  have hfieldLimitBits' := hfieldLimitBits.degree_mono hdegree
  have hrowWidthBits' := hrowWidthBits.degree_mono hdegree
  have hinputArityBits' := hinputArityBits
  have htailSix := hcountBits'.natBitLength_pair hboundBits'
  have htailFive := hwidthBits'.natBitLength_pair htailSix
  have htailFour := hfieldLimitBits'.natBitLength_pair htailFive
  have htailThree := hrowWidthBits'.natBitLength_pair htailFour
  have htailTwo := hinputArityBits'.natBitLength_pair htailThree
  have htailOne := htable'.natBitLength_pair htailTwo
  have hrequest :
      Dominated (fun request : Request =>
        natBitLength
          (structuralCompilerCoreInput (outputs request) (width request)
            (count request) (bound request) request.index))
        measureOf (degree + degree) := by
    simpa [structuralCompilerCoreInput, selectiveCountCasesInput,
      structuralRowWidth] using hstateBits'.natBitLength_pair htailOne
  obtain ⟨coefficient, hrequest⟩ := hrequest
  refine ⟨coefficient, ?_⟩
  intro target index hindexLt
  simpa [totalInverseCanonicalCompilerRequestBits, outputs, width, count, bound,
    measureOf, liveMeasure] using
    hrequest
      ({ target := target, index := index, isLt := hindexLt } : Request)

end NearCubicWires.TotalInverseCanonicalCompilerRequestResources
