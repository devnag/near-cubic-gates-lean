import Proof.CaseAnalysis.FinalWorkerDockBody

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **The phase's whole call stream**: the concatenation, over PCPP clause
addresses, of the per-address record lists of S1.  This is the list the
clause-address driver accumulates and the multiply stage reads. -/
noncomputable def phaseRecords {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) : List Entry :=
  (univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.flatMap
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)

/-- **The seam.**  S1's call production and W2's docked body inhabit W1's
`Realizes` for the composed machine: one run, one budget, one port.

The bank is `RepairCloseoutFinalC10WorkerDock`'s (`Fin 218`, `input = 0`,
`flag = 216`, `result = 217`, `port = 215`); the width is the fold's own
(`foldWidth`), which is W1's frozen choice; the call stream is S1's, indexed by
PCPP clause addresses.  Nothing here chooses a constant. -/
noncomputable def worker_dock_realizes {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm}
    {loaderStates emitStates : ℕ}
    (phase : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput arity → Bool)
    (proofValue :
      BitInput arity → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (supplier : List Atom → ℚ) (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (hcount : ∀ factors : List Atom, answer factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth) (hdenominatorPositive : 0 < denominator)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address))
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤
        failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ mass)
    (hbudget : failure * mass ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (onset : ℕ) (loader : Machine 218 loaderStates) (emitLoader : Machine 218 emitStates)
    (loaderFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (hruns : BodyRuns onset entryWidth loader emitLoader loaderFuel emitFuel len x bits
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom)) :
    Realizes phase constants pcpp proofValue evaluate
      (worker onset inputTape flag result (fullBody loader emitLoader))
      (workerBudget onset
        (fullBodyFuel loaderFuel emitFuel entryWidth
          (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
        len)
      (fun _ => 0)
      ((UAcceptanceCarrier.verifier
        (worker onset inputTape flag result (fullBody loader emitLoader))
        dockTapes_two result).inputTapes (List.ofFn x) bits)
      port
      (foldWidth (CompetitorRationalDecision.width entryWidth)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom)) :=
  worker_realizes phase constants pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic supplier failure hfailure hpoint mass hmass hbudget
    onset inputTape flag result port (fullBody loader emitLoader) dockTapes_two
    inputTape_val
    (fullBodyFuel loaderFuel emitFuel entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
    (foldWidth (CompetitorRationalDecision.width entryWidth)
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
    (CompetitorRationalDecision.width entryWidth) len x bits honset
    (estimator_body_of_runs onset entryWidth loader emitLoader loaderFuel emitFuel len x
      bits supplier (phasePolynomial phase pcpp coordinate systematicAtom)
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom)
      (phase_calls phase pcpp coordinate systematicAtom supplier answer denominator
        hsupplier)
      (phase_records_valid phase pcpp coordinate systematicAtom answer denominator
        entryWidth hcount hdenominator hdenominatorPositive hcoefficients)
      hruns)

theorem worker_dock_accurate {Atom : Type} {arity : ℕ}
    {circuit : BooleanCircuit arity} {source : PointwisePCPPAlgorithm}
    {loaderStates emitStates : ℕ}
    (phase : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput arity → Bool)
    (proofValue :
      BitInput arity → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (supplier : List Atom → ℚ) (answer : List Atom → ℕ)
    (denominator entryWidth : ℕ)
    (hsupplier : ∀ factors : List Atom,
      ((answer factors : ℚ) / (denominator : ℚ)) = supplier factors)
    (hcount : ∀ factors : List Atom, answer factors < 2 ^ entryWidth)
    (hdenominator : denominator < 2 ^ entryWidth) (hdenominatorPositive : 0 < denominator)
    (hcoefficients : ∀ address : Fin (2 ^ pcpp.clauseBits),
      CoefficientsFit entryWidth (siteCalls phase pcpp coordinate systematicAtom address))
    (failure : ℝ) (hfailure : 0 ≤ failure)
    (hpoint : ∀ circuits : List Atom,
      |((supplier circuits : ℚ) : ℝ) - conjunctionProbability evaluate circuits| ≤
        failure)
    (mass : ℝ)
    (hmass : (((phasePolynomial phase pcpp coordinate systematicAtom).coefficientMass :
      ℚ) : ℝ) ≤ mass)
    (hbudget : failure * mass ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ))
    (onset : ℕ) (loader : Machine 218 loaderStates) (emitLoader : Machine 218 emitStates)
    (loaderFuel emitFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (honset : onset ≤ len)
    (hruns : BodyRuns onset entryWidth loader emitLoader loaderFuel emitFuel len x bits
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom)) :
    |(((CompetitorSumFold.folded CompetitorSumWidth.zero
          (contributions
            (phaseRecords answer denominator phase pcpp coordinate
              systematicAtom))).value : ℚ) : ℝ) -
        CloseoutRowsOriginalSchedule.mean phase pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) :=
  worker_accurate phase constants pcpp evaluate proofValue coordinate hcoordinate
    systematicAtom hsystematic supplier failure hfailure hpoint mass hmass hbudget
    onset inputTape flag result port (fullBody loader emitLoader) dockTapes_two
    inputTape_val
    (fullBodyFuel loaderFuel emitFuel entryWidth
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length)
    (foldWidth (CompetitorRationalDecision.width entryWidth)
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
    (CompetitorRationalDecision.width entryWidth) len x bits honset
    (estimator_body_of_runs onset entryWidth loader emitLoader loaderFuel emitFuel len x
      bits supplier (phasePolynomial phase pcpp coordinate systematicAtom)
      (phaseRecords answer denominator phase pcpp coordinate systematicAtom)
      (phase_calls phase pcpp coordinate systematicAtom supplier answer denominator
        hsupplier)
      (phase_records_valid phase pcpp coordinate systematicAtom answer denominator
        entryWidth hcount hdenominator hdenominatorPositive hcoefficients)
      hruns)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
