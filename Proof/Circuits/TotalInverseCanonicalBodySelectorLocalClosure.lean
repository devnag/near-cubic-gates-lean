import Proof.Circuits.TotalInverseCanonicalBodySelectorResources

/-! # Closing the five canonical selector heads from their component ledgers -/

namespace NearCubicWires.TotalInverseCanonicalBodySelectorLocalClosure

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorCanonicalResourceFrontier
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SourceDrivenNumeralBank
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseCanonicalBodySelectorResources
open NearCubicWires.TotalInverseCanonicalCompiledBodyResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseCanonicalRangeResources
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TotalStructuralAtomEmitterProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

open private satTagBits satTagProgram from Proof.MachineModel.BankRecoveryCodeProgram

private abbrev Request := LanguageEvaluationRequest
private def measureOf (request : Request) : ℕ := request.measure

noncomputable def canonicalPointSourceLength
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  sourceLength
    (inverseChainSourceIndex contracts clockDepth advantageExponent
      request.length)

noncomputable def canonicalPointScheduledWidth
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  scheduledWidth (publishedHierarchyOuterPCP contracts clockDepth)
    (inverseChainSourceIndex contracts clockDepth advantageExponent
      request.length)

noncomputable def canonicalPointQueryCount
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  (publishedHierarchyOuterPCP contracts clockDepth).pcp.queryCount
    (canonicalPointSourceLength contracts clockDepth advantageExponent request)

noncomputable def canonicalPointCopies
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  inverseCopies (publishedHierarchyOuterPCP contracts clockDepth)
    (publishedPointwisePCPP contracts)
    (inverseBankRate contracts advantageExponent)
    (inverseChainSourceIndex contracts clockDepth advantageExponent
      request.length)

noncomputable def canonicalBodyAdapterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) : Request → ℕ :=
  totalInverseSelectorBodyAdapterBits contracts clockDepth machine
    advantageExponent pcp
    (totalInverseCanonicalCompilerBits contracts clockDepth machine
      advantageExponent pcp)

noncomputable def canonicalBodyAtomEmitterBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) : Request → ℕ :=
  fun request =>
    totalStructuralAtomEmitterBits
      (totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp request.length)
      request.length
      (inverseAtomCount contracts clockDepth machine advantageExponent pcp
        request.length)
      (inverseAtomContext contracts clockDepth machine advantageExponent pcp
        request.length)
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
        request)
      (inverseSelectorAtoms contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent request.length)

noncomputable def canonicalBodyAdapterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) : Request → ℕ :=
  totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
    advantageExponent pcp
    (totalInverseCanonicalCompilerFuel contracts clockDepth machine
      advantageExponent pcp)

noncomputable def canonicalBodyAtomEmitterFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) : Request → ℕ :=
  totalInverseAtomEmitterFuel contracts clockDepth machine advantageExponent pcp
    (totalInverseCanonicalCompilerFuel contracts clockDepth machine
      advantageExponent pcp)

noncomputable def canonicalBodyAtomCode
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  encodeTaggedList
    (boundedOracleStructuralFormulaAtoms
      (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
      (inverseRefuterInput contracts
        (publishedHierarchyOuterPCP contracts clockDepth) machine
        advantageExponent request.length)
      (inverseScheduleBound contracts clockDepth advantageExponent
        request.length))

noncomputable def canonicalBodyRecoveryCode
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  boundedOracleRecoveryCode
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent request.length)

noncomputable def canonicalBodyRecoveryCodeBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  recoveryCodeBits
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent request.length)
    request.length

noncomputable def canonicalBodyRecoveryCodeFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  recoveryCodeFuel
    (paddedOuterPCP (publishedHierarchyOuterPCP contracts clockDepth))
    (inverseRefuterInput contracts
      (publishedHierarchyOuterPCP contracts clockDepth) machine
      advantageExponent request.length)
    (inverseScheduleBound contracts clockDepth advantageExponent request.length)

def CanonicalBodySelectorComponentFrontierDominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) (degree : ℕ) : Prop :=
  Dominated (fun request => natBitLength
      (canonicalPointSourceLength contracts clockDepth advantageExponent
        request)) measureOf degree ∧
    Dominated (fun request => natBitLength
      (canonicalPointScheduledWidth contracts clockDepth advantageExponent
        request)) measureOf degree ∧
    Dominated (fun request => natBitLength
      (canonicalPointQueryCount contracts clockDepth advantageExponent
        request)) measureOf degree ∧
    Dominated (fun request => natBitLength
      (canonicalPointCopies contracts clockDepth advantageExponent request))
      measureOf degree ∧
    Dominated
      (canonicalBodyAdapterBits contracts clockDepth machine advantageExponent
        pcp) measureOf degree ∧
    Dominated
      (canonicalBodyAtomEmitterBits contracts clockDepth machine
        advantageExponent pcp) measureOf degree ∧
    Dominated
      (canonicalBodyAdapterFuel contracts clockDepth machine advantageExponent
        pcp) measureOf degree ∧
    Dominated
      (canonicalBodyAtomEmitterFuel contracts clockDepth machine
        advantageExponent pcp) measureOf degree ∧
    Dominated
      (canonicalBodyRecoveryCodeBits contracts clockDepth machine
        advantageExponent) measureOf degree ∧
    Dominated (fun request => natBitLength
      (canonicalBodyAtomCode contracts clockDepth machine advantageExponent
        request)) measureOf degree ∧
    Dominated (fun request => natBitLength
      (canonicalBodyRecoveryCode contracts clockDepth machine advantageExponent
        request)) measureOf degree ∧
    Dominated
      (canonicalBodyRecoveryCodeFuel contracts clockDepth machine
        advantageExponent) measureOf degree

set_option maxRecDepth 20000 in
-- The component aliases preserve several nested schedule-dependent frames.
set_option maxHeartbeats 800000 in
-- Exact normalization retains the canonical compiler, range, and PCP terms.
theorem canonicalBodySelectorLocalFrontier_dominated_of_components
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp : ExecutableProjectionPCP
      (publishedRefuterSource contracts clockDepth).hierarchyMachine
      (pairClock clockDepth)) (degree : ℕ) (hdegree : 1 ≤ degree)
    (hcomponents : CanonicalBodySelectorComponentFrontierDominated contracts
      clockDepth machine advantageExponent pcp degree) :
    CanonicalBodySelectorLocalFrontierDominated contracts clockDepth machine
      advantageExponent pcp degree := by
  rcases hcomponents with
    ⟨hsourceLength, hscheduleWidth, hqueryCount, hcopies,
      hadapterBits, hatomEmitterBits, hadapterFuel, hatomEmitterFuel,
      hrecoveryBits, hatomCode, hrecoveryCode, hrecoveryFuel⟩
  have hlength : Dominated (fun request : Request => natBitLength request.length)
      measureOf degree :=
    ⟨1, fun request =>
      (requestLengthBits_polyBounded request).degree_mono hdegree⟩
  have hcode : Dominated (fun request : Request => natBitLength request.code)
      measureOf degree := by
    refine ⟨1, fun request => (show PolyBounded (natBitLength request.code)
      request.measure 1 1 from ?_).degree_mono hdegree⟩
    unfold PolyBounded
    simp only [pow_one, Nat.one_mul]
    exact (natBitLength_encodeBitInput_le request.input).trans (by
      simp only [LanguageEvaluationRequest.measure]
      omega)
  have hpoint : Dominated
      (totalInverseCanonicalCompiledBodyPointBits contracts clockDepth
        advantageExponent) measureOf degree := by
    have hframe := hsourceLength.natBitLength_pair
      (hscheduleWidth.natBitLength_pair
        (hqueryCount.natBitLength_pair (hcopies.natBitLength_pair hcode)))
    change Dominated
      (fun request : Request => natBitLength
        (scheduleNumeralBankOutput
          (canonicalPointSourceLength contracts clockDepth advantageExponent
            request)
          (canonicalPointScheduledWidth contracts clockDepth advantageExponent
            request)
          (canonicalPointQueryCount contracts clockDepth advantageExponent
            request)
          (canonicalPointCopies contracts clockDepth advantageExponent request)
          request.code)) measureOf degree
    exact hframe
  have hemitterBits : Dominated
      (canonicalBodyEmitterBits contracts clockDepth machine advantageExponent
        pcp) measureOf degree := by
    change Dominated
      (fun request : Request => occurrenceStageBits request.length
        (canonicalBodyAdapterBits contracts clockDepth machine
          advantageExponent pcp request)
        (canonicalBodyAtomEmitterBits contracts clockDepth machine
          advantageExponent pcp request)) measureOf degree
    exact hlength.occurrenceStageBits hadapterBits hatomEmitterBits
  have hemitterFuel : Dominated
      (canonicalBodyEmitterFuel contracts clockDepth machine advantageExponent
        pcp) measureOf degree := by
    change Dominated
      (fun request : Request => linkFuel totalStructuralAtomEmitterProgram
        (canonicalBodyAdapterFuel contracts clockDepth machine
          advantageExponent pcp request)
        (canonicalBodyAtomEmitterFuel contracts clockDepth machine
          advantageExponent pcp request)) measureOf degree
    exact Dominated.linkFuel (second := totalStructuralAtomEmitterProgram)
      hadapterFuel hatomEmitterFuel
  have hqueryBits : Dominated
      (canonicalBodyQueryBits contracts clockDepth machine advantageExponent)
      measureOf degree := by
    have hentry := hatomCode.natBitLength_pair hpoint
    have hexit := hrecoveryCode.natBitLength_pair hpoint
    have hpreserved := hrecoveryBits.preserveRightBits hentry hexit
    have hbool : Dominated (fun request : Request =>
        natBitLength
          (encodedSat
            (canonicalBodyRecoveryCode contracts clockDepth machine
              advantageExponent request)).toNat) measureOf degree :=
      (dominated_const (natBitLength 1) degree).mono fun request =>
        natBitLength_mono (by
          cases encodedSat
            (canonicalBodyRecoveryCode contracts clockDepth machine
              advantageExponent request) <;> simp)
    have htaggedInput := hrecoveryCode.natBitLength_pair hpoint
    have htaggedOutput := hbool.natBitLength_pair hpoint
    have hsat := htaggedInput.natBitLength_max htaggedOutput
    change Dominated
      (fun request : Request => occurrenceStageBits request.length
        (preserveRightBits
          (canonicalBodyRecoveryCodeBits contracts clockDepth machine
            advantageExponent request)
          (canonicalBodyAtomCode contracts clockDepth machine
            advantageExponent request)
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request)
          (canonicalBodyRecoveryCode contracts clockDepth machine
            advantageExponent request))
        (satTagBits
          (canonicalBodyRecoveryCode contracts clockDepth machine
            advantageExponent request)
          (inverseSelectorAdapterFrame contracts clockDepth advantageExponent
            request))) measureOf degree
    exact hlength.occurrenceStageBits hpreserved hsat
  have hqueryFuel : Dominated
      (canonicalBodyQueryFuel contracts clockDepth machine advantageExponent)
      measureOf degree := by
    have hpreserved := hrecoveryFuel.preserveRightFuel
    have hfive : Dominated (fun _ : Request => 5) measureOf degree :=
      dominated_const 5 degree
    change Dominated
      (fun request : Request => linkFuel satTagProgram
        (preserveRightFuel
          (canonicalBodyRecoveryCodeFuel contracts clockDepth machine
            advantageExponent request)) 5) measureOf degree
    exact Dominated.linkFuel (second := satTagProgram) hpreserved hfive
  exact ⟨hpoint, hemitterBits, hqueryBits, hemitterFuel, hqueryFuel⟩

end NearCubicWires.TotalInverseCanonicalBodySelectorLocalClosure
