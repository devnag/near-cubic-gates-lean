import Proof.Circuits.InverseSelectorCanonicalResourceFrontier
import Proof.Circuits.TotalInverseCanonicalRangeResources

namespace NearCubicWires.TotalInverseCanonicalCompiledBodyResources

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.InverseSelectorCanonicalResourceFrontier
open NearCubicWires.InverseSelectorOccurrenceEncodingClosure
open NearCubicWires.InverseSubstitutionRequestWordClosure
open NearCubicWires.InverseTotalScheduledRowStageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenBodyDispatch
open NearCubicWires.SelectorDrivenRegisterTargetChainBase
open NearCubicWires.TotalBankEmittedAtomLoop
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseCanonicalCompiledBodyRun
open NearCubicWires.TotalInverseCanonicalRangeResources
open NearCubicWires.TotalInverseSelectorAtomStreamClosure
open NearCubicWires.TotalInverseSelectorCompiledBody
open NearCubicWires.TotalInverseSelectorDirectBodyClosure
open NearCubicWires.TotalSelectorBodyAdapter
open NearCubicWires.TotalSelectorDrivenEmitterResources
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.UniformTargetTotalRun
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

private abbrev Request := LanguageEvaluationRequest

private def measureOf (request : Request) : ℕ := request.measure

noncomputable def totalInverseCanonicalCompiledBodyPointBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (advantageExponent : ℝ) (request : Request) : ℕ :=
  natBitLength
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent request)

noncomputable def totalInverseCanonicalCompiledBodySelectorBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : Request) : ℕ :=
  inverseBankSelectorBitsAtFrame contracts clockDepth machine advantageExponent
    (inverseSelectorAdapterFrame contracts clockDepth advantageExponent)
    (totalInverseSelectorBankEmitterBits contracts clockDepth machine
      advantageExponent pcp
      (totalInverseSelectorBodyAdapterBits contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerBits contracts clockDepth machine
          advantageExponent pcp))
      (totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp)) request

noncomputable def totalInverseCanonicalCompiledBodyChainBits
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : Request) : ℕ :=
  inverseSelectorDirectChainBits contracts clockDepth machine
    advantageExponent
    (inverseTotalScheduledRowBits contracts clockDepth machine
      advantageExponent)
    (inverseSelectorOccurrenceBitsOfEncoding contracts clockDepth machine
      advantageExponent
      (inverseSelectorClosedEncodingBits contracts clockDepth machine
        advantageExponent
        (totalInverseSelectorAtomStreamBits contracts clockDepth machine
          advantageExponent pcp
          (totalInverseCanonicalRangeBits contracts clockDepth machine
            advantageExponent pcp)
          (totalInverseCanonicalCompilerBits contracts clockDepth machine
            advantageExponent pcp)))) request

noncomputable def totalInverseCanonicalCompiledBodySelectorFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : Request) : ℕ :=
  inverseBankSelectorFuel contracts clockDepth machine advantageExponent
    (totalInverseBankEmitterFuel contracts clockDepth machine advantageExponent
      pcp
      (totalInverseSelectorBodyAdapterFuel contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFuel contracts clockDepth machine
          advantageExponent pcp))
      (totalInverseCanonicalCompilerFuel contracts clockDepth machine
        advantageExponent pcp)) request

noncomputable def totalInverseCanonicalCompiledBodyChainFuel
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (request : Request) : ℕ :=
  inverseSelectorDirectChainFuel contracts clockDepth machine advantageExponent
    (inverseTotalScheduledRowProgram contracts clockDepth)
    (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
      advantageExponent
      (inverseSelectorClosedEncodingProgram contracts clockDepth machine
        advantageExponent
        (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
          advantageExponent pcp)))
    (inverseTotalScheduledRowFuel contracts clockDepth machine
      advantageExponent)
    (inverseSelectorOccurrenceFuelOfEncoding contracts clockDepth machine
      advantageExponent
      (inverseSelectorClosedEncodingProgram contracts clockDepth machine
        advantageExponent
        (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
          advantageExponent pcp))
      (inverseSelectorClosedEncodingFuel contracts clockDepth machine
        advantageExponent
        (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
          advantageExponent pcp)
        (totalInverseSelectorAtomStreamFuel contracts clockDepth machine
          advantageExponent pcp
          (totalInverseCanonicalCompilerFuel contracts clockDepth machine
            advantageExponent pcp)))) request

def CanonicalCompiledBodyTopFrontierDominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ) : Prop :=
  Dominated
      (totalInverseCanonicalCompiledBodyPointBits contracts clockDepth
        advantageExponent) measureOf degree ∧
    Dominated
      (totalInverseCanonicalCompiledBodySelectorBits contracts clockDepth
        machine advantageExponent pcp) measureOf degree ∧
    Dominated
      (totalInverseCanonicalCompiledBodyChainBits contracts clockDepth machine
        advantageExponent pcp) measureOf degree ∧
    Dominated
      (totalInverseCanonicalCompiledBodySelectorFuel contracts clockDepth
        machine advantageExponent pcp) measureOf degree ∧
    Dominated
      (totalInverseCanonicalCompiledBodyChainFuel contracts clockDepth machine
        advantageExponent pcp) measureOf degree

/-! The six-way range also closes the exact totality consumer outright. -/
theorem totalBooleanRuns_totalInverseCanonicalCompiledBody
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (hpresentation :
      PresentsPaddedOuterPCP
        (publishedHierarchyOuterPCP contracts clockDepth) pcp) :
    TotalBooleanRuns
      (totalInverseSelectorCompiledBody contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseSelectorCompiledBodyBits contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalRangeBits contracts clockDepth machine
          advantageExponent pcp)
        (totalInverseCanonicalCompilerBits contracts clockDepth machine
          advantageExponent pcp))
      (totalInverseSelectorCompiledBodyFuel contracts clockDepth machine
        advantageExponent pcp
        (totalInverseCanonicalCompilerFuel contracts clockDepth machine
          advantageExponent pcp))
      (inverseSelectorAdapterFrame contracts clockDepth advantageExponent) := by
  exact
    totalBooleanRuns_totalInverseSelectorCompiledBody_canonicalCompiler
      contracts clockDepth machine advantageExponent pcp hpresentation
      (totalInverseCanonicalRangeBits contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalRangeBits_positive contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalRangeBits_length contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalRangeBits_generated contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalRangeBits_list contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalRangeBits_call contracts clockDepth machine
        advantageExponent pcp)
      (totalInverseCanonicalRangeBits_callee contracts clockDepth machine
        advantageExponent pcp)

private theorem dominated_requestLengthBits (degree : ℕ) (hdegree : 1 ≤ degree) :
    Dominated (fun request : Request => natBitLength request.length) measureOf
      degree :=
  ⟨1, fun request =>
    (requestLengthBits_polyBounded request).degree_mono hdegree⟩

private theorem dominated_tagBits (tag degree : ℕ) :
    Dominated (fun _ : Request => natBitLength tag) measureOf degree :=
  dominated_const (natBitLength tag) degree

set_option maxHeartbeats 800000 in
-- The final two `simpa` calls align the five frozen heads with the exact body.
theorem totalInverseCanonicalCompiledBodyResources_dominated
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (degree : ℕ) (hdegree : 1 ≤ degree)
    (hfrontier : CanonicalCompiledBodyTopFrontierDominated contracts clockDepth
      machine advantageExponent pcp degree) :
    ∃ bitsCoefficient fuelCoefficient,
      (∀ request : Request,
        PolyBounded
          (totalInverseSelectorCompiledBodyBits contracts clockDepth machine
            advantageExponent pcp
            (totalInverseCanonicalRangeBits contracts clockDepth machine
              advantageExponent pcp)
            (totalInverseCanonicalCompilerBits contracts clockDepth machine
              advantageExponent pcp) request)
          request.measure bitsCoefficient degree) ∧
      (∀ request : Request,
        PolyBounded
          (totalInverseSelectorCompiledBodyFuel contracts clockDepth machine
            advantageExponent pcp
            (totalInverseCanonicalCompilerFuel contracts clockDepth machine
              advantageExponent pcp) request)
          request.measure fuelCoefficient degree) := by
  rcases hfrontier with
    ⟨hpoint, hselectorBits, hchainBits, hselectorFuel, hchainFuel⟩
  have hlength := dominated_requestLengthBits degree hdegree
  have htagZero := dominated_tagBits 0 degree
  have htagOne := dominated_tagBits 1 degree
  have houtput := dominated_tagBits 1 degree
  have htaggedZero := htagZero.natBitLength_pair hpoint
  have htaggedOne := htagOne.natBitLength_pair hpoint
  have hrequestZero := hlength.natBitLength_pair htaggedZero
  have hrequestOne := hlength.natBitLength_pair htaggedOne
  have hchoiceZero := hrequestZero.max (hchainBits.max houtput)
  have hchoiceOne := hrequestOne.max (hchainBits.max houtput)
  have hbranchZero := hlength.max (hselectorBits.max hchoiceZero)
  have hbranchOne := hlength.max (hselectorBits.max hchoiceOne)
  have hbits := hbranchZero.max hbranchOne
  obtain ⟨bitsCoefficient, hbits⟩ := hbits
  obtain ⟨selectorFuelCoefficient, hselectorFuel⟩ := hselectorFuel
  obtain ⟨chainFuelCoefficient, hchainFuel⟩ := hchainFuel
  let first := inverseSelectorCaseOneProgram contracts clockDepth machine
    (inverseTotalScheduledRowProgram contracts clockDepth)
  let second := inverseSelectorCaseTwoProgram contracts
    (inverseSelectorOccurrenceProgramOfEncoding contracts clockDepth
      advantageExponent
      (inverseSelectorClosedEncodingProgram contracts clockDepth machine
        advantageExponent
        (totalInverseSelectorAtomStreamProgram contracts clockDepth machine
          advantageExponent pcp)))
  let fuelCoefficient :=
    programRegisterSpan (taggedProgramChoice first second) + 5 +
      selectorFuelCoefficient + (chainFuelCoefficient + 5)
  have hfuel : ∀ request : Request,
      PolyBounded
        (branchTargetBitFuel first second
          (totalInverseCanonicalCompiledBodySelectorFuel contracts clockDepth
            machine advantageExponent pcp request)
          (totalInverseCanonicalCompiledBodyChainFuel contracts clockDepth
            machine advantageExponent pcp request))
        request.measure fuelCoefficient degree := by
    intro request
    exact (linkFuel_polyBounded (second := taggedProgramChoice first second)
      (hselectorFuel request)
      (taggedProgramChoiceFuel_polyBounded (hchainFuel request))).coefficient_mono
        (by dsimp only [fuelCoefficient]; omega)
  refine ⟨bitsCoefficient, fuelCoefficient, ?_, ?_⟩
  · intro request
    simpa only [totalInverseSelectorCompiledBodyBits,
      totalInverseSelectorDirectBodyBits,
      totalInverseCanonicalCompiledBodyPointBits,
      totalInverseCanonicalCompiledBodySelectorBits,
      totalInverseCanonicalCompiledBodyChainBits,
      bankDispatchedBodyBitsAtFrame, branchTargetBitBits, branchChoiceBits,
      occurrenceStageBits, measureOf] using
      hbits request
  · intro request
    simpa only [totalInverseSelectorCompiledBodyFuel,
      totalInverseSelectorDirectBodyFuel,
      totalInverseCanonicalCompiledBodySelectorFuel,
      totalInverseCanonicalCompiledBodyChainFuel,
      bankDispatchedBodyFuel, first, second, measureOf] using hfuel request

end NearCubicWires.TotalInverseCanonicalCompiledBodyResources
