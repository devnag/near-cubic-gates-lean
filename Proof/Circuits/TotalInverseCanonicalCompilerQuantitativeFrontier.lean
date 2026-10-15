import Proof.Circuits.TotalInverseCanonicalCompilerRequestFieldReduction

namespace NearCubicWires.TotalInverseCanonicalCompilerQuantitativeFrontier

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BoundedOracleStructuralSelectiveCompiler
open NearCubicWires.BoundedOracleStructuralSelectiveProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.TotalInverseCanonicalCompilerForwardResources
open NearCubicWires.TotalInverseCanonicalCompilerRequestFieldReduction
open NearCubicWires.TotalInverseCanonicalCompilerRequestResources
open NearCubicWires.TotalInverseCanonicalCompilerResources
open NearCubicWires.TotalInverseCanonicalCompilerRuns
open NearCubicWires.TotalInverseCanonicalFixedCountWalkDomination
open NearCubicWires.TotalInverseCanonicalLocalForwardBitsDomination
open NearCubicWires.ValidatorPolynomialDomination

open private canonicalOutputs canonicalWidth canonicalCount canonicalBound from
  Proof.Circuits.TotalInverseCanonicalCompilerResources

theorem totalInverseCanonicalCompiler_dominated_of_sourceFrontier
    (contracts : PublishedContracts) (clockDepth : ℕ)
    (machine : ExecutableWeakNondeterministicMachine)
    (advantageExponent : ℝ)
    (pcp :
      ExecutableProjectionPCP
        (publishedRefuterSource contracts clockDepth).hierarchyMachine
        (pairClock clockDepth))
    (sourceDegree fixedBitsDegree fixedFuelDegree localBitsDegree : ℕ)
    (fixedBitsMaximum fixedFuelMaximum localBitsMaximum : ℕ → ℕ → ℕ)
    (hsources : CanonicalCompilerRequestSourcesDominated contracts clockDepth
      machine advantageExponent pcp sourceDegree)
    (hfixedBitsWithin : CanonicalFixedCountWalkBitsWithin contracts clockDepth
      machine advantageExponent pcp fixedBitsMaximum)
    (hfixedBitsMaximum : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp fixedBitsMaximum coefficient fixedBitsDegree)
    (hfixedFuelWithin : CanonicalFixedCountWalkFuelWithin contracts clockDepth
      machine advantageExponent pcp fixedFuelMaximum)
    (hfixedFuelMaximum : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp fixedFuelMaximum coefficient fixedFuelDegree)
    (hlocalBitsWithin : CanonicalLocalForwardBitsWithin contracts clockDepth
      machine advantageExponent pcp localBitsMaximum)
    (hlocalBitsMaximum : ∃ coefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
        advantageExponent pcp localBitsMaximum coefficient localBitsDegree) :
    let requestDegree := sourceDegree *
      2 ^ oracleDepth
        (inverseRequiredDegree contracts
          (inverseCoreAdvantagePower advantageExponent))
    let bitsDegree :=
      (requestDegree + requestDegree) + fixedBitsDegree + localBitsDegree
    let fuelDegree := requestDegree + fixedFuelDegree
    ∃ bitsCoefficient fuelCoefficient,
      CanonicalCompilerPolyBounded contracts clockDepth machine
          advantageExponent pcp
          (totalInverseCanonicalCompilerBits contracts clockDepth machine
            advantageExponent pcp)
          bitsCoefficient bitsDegree ∧
        CanonicalCompilerPolyBounded contracts clockDepth machine
          advantageExponent pcp
          (totalInverseCanonicalCompilerFuel contracts clockDepth machine
            advantageExponent pcp)
          fuelCoefficient fuelDegree := by
  let requestDegree := sourceDegree *
    2 ^ oracleDepth
      (inverseRequiredDegree contracts
        (inverseCoreAdvantagePower advantageExponent))
  let bitsDegree :=
    (requestDegree + requestDegree) + fixedBitsDegree + localBitsDegree
  let fuelDegree := requestDegree + fixedFuelDegree
  have hfields : CanonicalCompilerRequestFieldsDominated contracts clockDepth
      machine advantageExponent pcp requestDegree := by
    simpa [requestDegree] using
      canonicalCompilerRequestFieldsDominated_of_sources contracts clockDepth
        machine advantageExponent pcp sourceDegree hsources
  obtain ⟨requestCoefficient, hrequest⟩ :=
    totalInverseCanonicalCompilerRequestBits_dominated contracts clockDepth
      machine advantageExponent pcp requestDegree hfields
  obtain ⟨fixedBitsCoefficient, hfixedBitsMaximum⟩ := hfixedBitsMaximum
  have hfixedBits :=
    totalInverseCanonicalFixedCountWalkBits_dominated_of_callsWithin
      contracts clockDepth machine advantageExponent pcp fixedBitsMaximum
      fixedBitsCoefficient fixedBitsDegree hfixedBitsWithin hfixedBitsMaximum
  obtain ⟨localBitsCoefficient, hlocalBitsMaximum⟩ := hlocalBitsMaximum
  have hlocalBits :=
    totalInverseCanonicalCompilerLocalForwardBits_dominated_of_within
      contracts clockDepth machine advantageExponent pcp localBitsMaximum
      localBitsCoefficient localBitsDegree hlocalBitsWithin hlocalBitsMaximum
  have hrequest' : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerRequestBits contracts clockDepth machine
        advantageExponent pcp) requestCoefficient bitsDegree := by
    intro target index hindex
    exact (hrequest target index hindex).degree_mono (by
      dsimp only [bitsDegree]
      omega)
  have hfixedBits' : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerFixedCountWalkBits contracts clockDepth
        machine advantageExponent pcp) fixedBitsCoefficient bitsDegree := by
    intro target index hindex
    exact (hfixedBits target index hindex).degree_mono (by
      dsimp only [bitsDegree]
      omega)
  have hlocalBits' : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerLocalForwardBits contracts clockDepth
        machine advantageExponent pcp) localBitsCoefficient bitsDegree := by
    intro target index hindex
    exact (hlocalBits target index hindex).degree_mono (by
      dsimp only [bitsDegree]
      omega)
  obtain ⟨forwardBitsCoefficient, hforwardBits⟩ :=
    totalInverseCanonicalCompilerForwardBits_dominated_of_fixedCountFrontier
      contracts clockDepth machine advantageExponent pcp bitsDegree
      ⟨fixedBitsCoefficient, hfixedBits'⟩
      ⟨localBitsCoefficient, hlocalBits'⟩
  have hbits := totalInverseCanonicalCompilerBits_polyBounded_of_frontier
    contracts clockDepth machine advantageExponent pcp requestCoefficient
    forwardBitsCoefficient bitsDegree hrequest' hforwardBits
  rcases hfields with ⟨_, _, _, hbound, _⟩
  let Request := CanonicalCompilerLiveIndex contracts clockDepth machine
    advantageExponent pcp
  change Dominated (fun request : Request =>
      canonicalBound contracts clockDepth advantageExponent request.target)
    (fun request : Request => max 1 request.target) requestDegree at hbound
  obtain ⟨boundCoefficient, hbound⟩ := hbound
  obtain ⟨fixedFuelCoefficient, hfixedFuelMaximum⟩ := hfixedFuelMaximum
  have hfixedFuel : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
        machine advantageExponent pcp)
      (boundCoefficient * fixedFuelCoefficient) fuelDegree := by
    intro target index hindex
    let request : Request := ⟨target, index, hindex⟩
    have hproduct := (hbound request).mul
      (hfixedFuelMaximum target index hindex)
    exact hproduct.mono <| by
      calc
        totalInverseCanonicalCompilerFixedCountWalkFuel contracts clockDepth
            machine advantageExponent pcp target index ≤
          (List.ofFn
            (id : Fin
              (canonicalBound contracts clockDepth advantageExponent target) →
                Fin
                  (canonicalBound contracts clockDepth advantageExponent
                    target))).length * fixedFuelMaximum target index :=
          selectiveFixedCountWalkFuel_le_of_within _ _ _ _ _ _ _ _
            (hfixedFuelWithin target index hindex)
        _ = canonicalBound contracts clockDepth advantageExponent target *
            fixedFuelMaximum target index := by simp
  have hforwardFuel : CanonicalCompilerPolyBounded contracts clockDepth machine
      advantageExponent pcp
      (totalInverseCanonicalCompilerForwardFuel contracts clockDepth machine
        advantageExponent pcp)
      ((boundCoefficient * fixedFuelCoefficient) +
        (56 * boundCoefficient + 32)) fuelDegree := by
    intro target index hindex
    let request : Request := ⟨target, index, hindex⟩
    rw [totalInverseCanonicalCompilerForwardFuel_eq_fixedCountFrontier]
    apply (hfixedFuel target index hindex).add
    have hlocal : PolyBounded
        (56 * canonicalBound contracts clockDepth advantageExponent target + 32)
        (max 1 target) (56 * boundCoefficient + 32) fuelDegree :=
      ((hbound request).degree_mono (by
          dsimp only [fuelDegree]
          omega)).const_mul 56 |>.add
        (polyBounded_const 32 (max 1 target) fuelDegree)
    exact hlocal.mono
      (totalInverseCanonicalCompilerLocalForwardFuel_le contracts clockDepth
        machine advantageExponent pcp target index)
  refine ⟨max requestCoefficient forwardBitsCoefficient,
    17 + ((boundCoefficient * fixedFuelCoefficient) +
      (56 * boundCoefficient + 32)), hbits, ?_⟩
  exact totalInverseCanonicalCompilerFuel_polyBounded_of_frontier
    contracts clockDepth machine advantageExponent pcp
    ((boundCoefficient * fixedFuelCoefficient) +
      (56 * boundCoefficient + 32)) fuelDegree hforwardFuel

end NearCubicWires.TotalInverseCanonicalCompilerQuantitativeFrontier
