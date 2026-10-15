import Proof.CaseAnalysis.FinalStability
import Proof.Hierarchy.CompetitorRationalTolerance
import Proof.CaseAnalysis.RowsEstimatorCoefficientsPrepare
import Proof.MachineModel.Runs

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairRepresentation
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Realizes {t s : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    {source : PointwisePCPPAlgorithm}
    (ph : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (evaluate : Atom → BitInput n → Bool)
    (p : Machine t s) (budget : ℕ) (hin : Fin t → ℕ) (tin : Fin t → List Bool)
    (port : Fin t) (width : ℕ) where
  /-- The expansion's index type -- the monomial positions. -/
  ι : Type
  index : Finset ι
  coefficient : ι → ℝ
  circuits : ι → List Atom
  estimate : ι → ℝ
  failure : ℝ
  mass : ℝ
  hfailure : 0 ≤ failure
  /-- **The paper's grouped phase mean IS this finite AND-four expansion.** -/
  hexpansion :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      ∑ i ∈ index, coefficient i * conjunctionProbability evaluate (circuits i)
  /-- The supplier answers every call within `failure`. -/
  hpoint : ∀ i ∈ index,
    |estimate i - conjunctionProbability evaluate (circuits i)| ≤ failure
  /-- The coefficient-mass ledger. -/
  hmass : (∑ i ∈ index, |coefficient i|) ≤ mass
  /-- Paper C.10.2: the propagated estimation error is below `eps_est`. -/
  hbudget :
    failure * mass ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ)
  heads : Fin t → ℕ
  exit : Fin t → List Bool
  /-- The physical receipt: ONE run, at this budget, from these tapes. -/
  run : Step p budget hin tin heads exit
  result : CompetitorValidity.Estimate
  hvalid : result.Valid width

  hencoded :
    exit port = CloseoutRowsEstimatorCoefficients.Stream.recordWord width result 1 1
  /-- The encoded output IS the expansion's estimated value. -/
  hvaluesum :
    ((result.value : ℚ) : ℝ) = ∑ i ∈ index, coefficient i * estimate i

theorem accurate_of_realizes {t s : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    {ph : CloseoutRowsOriginalSchedule.Phase} {constants : Constants source}
    {pcpp : PointwisePCPP circuit}
    {proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes ph constants pcpp proofValue evaluate p budget hin tin port
      width) :
    |((R.result.value : ℚ) : ℝ) -
        CloseoutRowsOriginalSchedule.mean ph pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  rw [R.hvaluesum, R.hexpansion]
  exact le_trans
    (componentwise_real_error R.index R.coefficient
      (fun i => conjunctionProbability evaluate (R.circuits i)) R.estimate
      R.failure R.mass R.hfailure R.hpoint R.hmass)
    R.hbudget

/-! ## The three `Exposes` conjuncts -/

theorem accurate_penalty {t s : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    {constants : Constants source} {pcpp : PointwisePCPP circuit}
    {proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes .penalty constants pcpp proofValue evaluate p budget hin tin
      port width) :
    |((R.result.value : ℚ) : ℝ) -
        AggregateSemanticStage.aggregateClausePenaltyMean pcpp proofValue / 2| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have h := accurate_of_realizes R
  rwa [CloseoutRowsOriginalSchedule.penalty_mean] at h

theorem accurate_moment {t s : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    {constants : Constants source} {pcpp : PointwisePCPP circuit}
    {proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes .moment constants pcpp proofValue evaluate p budget hin tin
      port width) :
    |((R.result.value : ℚ) : ℝ) -
        CompetitorSourceAverage.leftSecondMoment pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have h := accurate_of_realizes R
  rwa [CloseoutRowsOriginalSchedule.moment_mean] at h

theorem accurate_clause {t s : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    {constants : Constants source} {pcpp : PointwisePCPP circuit}
    {proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes .clause constants pcpp proofValue evaluate p budget hin tin
      port width) :
    |((R.result.value : ℚ) : ℝ) -
        AggregateSemanticStage.aggregateClauseMean pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  have h := accurate_of_realizes R
  rwa [CloseoutRowsOriginalSchedule.clause_mean] at h

/-- **`Realizes` from P3a + P3b + one physical receipt.**  This is the shape
the worker chain (W1) has to hit: everything semantic is already proved, so
the remaining obligation is exactly "run the machine, and leave
`recordWord width result 1 1` on `port`, with `result.value` the estimated
mean of the phase polynomial". -/
noncomputable def realizes_of_phasePolynomial {t s : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    (ph : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (supplier : List Atom → ℚ) (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) -
        conjunctionProbability evaluate circuits| ≤ failure)
    (mass : ℝ)
    (hmass :
      (((phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass :
        ℚ) : ℝ) ≤ mass)
    (hbudget :
      failure * mass ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (p : Machine t s) (budget : ℕ) (hin : Fin t → ℕ) (tin : Fin t → List Bool)
    (port : Fin t) (width : ℕ)
    (heads : Fin t → ℕ) (exit : Fin t → List Bool)
    (run : Step p budget hin tin heads exit)
    (result : CompetitorValidity.Estimate) (hvalid : result.Valid width)
    (hencoded : exit port =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord width result 1 1)
    (hvaluesum : ((result.value : ℚ) : ℝ) =
      (phasePolynomial ph pcpp coordinate systematicAtom).estimatedMean
        supplier) :
    Realizes ph constants pcpp proofValue evaluate p budget hin tin port width where
  ι := Fin (phasePolynomial ph pcpp coordinate systematicAtom).monomials.length
  index := univ
  coefficient := fun i =>
    (((phasePolynomial ph pcpp coordinate
      systematicAtom).monomials[i].coefficient : ℚ) : ℝ)
  circuits := fun i =>
    (phasePolynomial ph pcpp coordinate systematicAtom).monomials[i].factors
  estimate := fun i =>
    ((supplier (phasePolynomial ph pcpp coordinate
      systematicAtom).monomials[i].factors : ℚ) : ℝ)
  failure := failure
  mass := mass
  hfailure := hfailure
  hexpansion :=
    mean_eq_sum_conjunctionProbability ph pcpp evaluate proofValue coordinate
      hcoordinate systematicAtom hsystematic
  hpoint := fun i _ => hpoint _
  hmass := by
    rw [coefficientMass_eq_finsetSum]
    exact hmass
  hbudget := hbudget
  heads := heads
  exit := exit
  run := run
  result := result
  hvalid := hvalid
  hencoded := hencoded
  hvaluesum := by rw [hvaluesum, estimatedMean_eq_finsetSum]

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
