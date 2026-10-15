import Proof.CaseAnalysis.FinalWorkerEmit

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The fold's width trace ends on the final accumulator, so the answer is
valid at the trace's width. -/
theorem folded_valid (scalarWidth : ℕ) (start : CompetitorValidity.Estimate)
    (terms : List CompetitorValidity.Estimate)
    (htrace : CompetitorSumWidth.Trace scalarWidth start terms) :
    CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded start terms) scalarWidth := by
  induction terms generalizing start with
  | nil => exact htrace
  | cons term terms inductionHypothesis =>
      exact inductionHypothesis _ htrace.2.2

/-- **Constraint 10, settled.**  The estimator's answer is a valid `Estimate` at
the fold's own width; no fresh constant enters. -/
theorem answer_valid (recordWidth : ℕ) (entries : List Entry)
    (hvalid : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate recordWidth) :
    CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (foldWidth recordWidth entries) :=
  folded_valid _ _ _ (CompetitorSumWidth.uniform_trace recordWidth
    (contributions entries) hvalid)

/-- **The junction, one field shorter.**  At the fold's own width the validity
of the answer is a theorem, so `EstimatorBody` needs only the call stream, its
per-record validity, the physical receipt and the encoded output. -/
noncomputable def estimatorBody_ofFoldWidth {Atom : Type} {tapes bodyStates : ℕ}
    {body : Machine tapes bodyStates} {onset : ℕ}
    {input flag result port : Fin tapes} {htapes : 2 ≤ tapes} {fuel : ℕ → ℕ}
    {recordWidth : ℕ} {supplier : List Atom → ℚ}
    {polynomial : CircuitPolynomial Atom 4}
    {len : ℕ} {x : BitInput len} {bits : List Bool}
    (entries : List Entry) (heads : Fin tapes → ℕ) (exit : Fin tapes → List Bool)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hentries : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate recordWidth)
    (run : Step body (fuel len) (fun _ => 0)
      (exitTapes flag
        ((UAcceptanceCarrier.verifier (worker onset input flag result body) htapes
          result).inputTapes (List.ofFn x) bits) 0 true) heads exit)
    (hencoded : exit port =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord
        (foldWidth recordWidth entries)
        (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
        1 1) :
    EstimatorBody body onset input flag result port htapes fuel
      (foldWidth recordWidth entries) recordWidth supplier polynomial len x bits where
  entries := entries
  heads := heads
  exit := exit
  hcalls := hcalls
  hentries := hentries
  hfolded := answer_valid recordWidth entries hentries
  run := run
  hencoded := hencoded

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth
