import Proof.CaseAnalysis.FinalWorkerChain
import Proof.Hierarchy.CompetitorSumEntry

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 One supplier call per monomial -/

/-- **One call per monomial.**  The call stream is exactly as long as the
polynomial's monomial list, so the fold's driver runs one iteration per
monomial -- the paper's "expanding it into AND-four supplier calls", counted. -/
theorem calls_length {Atom : Type} {supplier : List Atom → ℚ}
    {monomials : List (CircuitMonomial Atom 4)} {entries : List Entry}
    (hcalls : List.Forall₂ (Calls supplier) monomials entries) :
    entries.length = monomials.length ∧
      (contributions entries).length = monomials.length := by
  have hlength : monomials.length = entries.length := hcalls.length_eq
  refine ⟨hlength.symm, ?_⟩
  rw [contributions, List.length_map, hlength]

/-! ## §2 The fold, as one real execution -/

def foldWidth (recordWidth : ℕ) (entries : List Entry) : ℕ :=
  CompetitorSumWidth.width (contributions entries).length recordWidth

theorem coldFold_estimatedMean {Atom : Type} (supplier : List Atom → ℚ)
    (recordWidth : ℕ) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hvalid : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate recordWidth) :
    ∃ receipt out,
      run CompetitorSumEntry.machine
          (CompetitorSumEntry.budget (foldWidth recordWidth entries)
            (contributions entries).length)
          (CompetitorSumEntry.input (foldWidth recordWidth entries)
            (contributions entries)) = some receipt ∧
        receipt.steps ≤ CompetitorSumEntry.budget (foldWidth recordWidth entries)
          (contributions entries).length ∧
        (∀ i : Fin 94, receipt.final.tapes (i.castAdd 1) = out i) ∧
        CompetitorSumFold.Store (foldWidth recordWidth entries)
          (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
          (CompetitorSumFold.words (foldWidth recordWidth entries)
            (contributions entries)) out ∧
        (((CompetitorSumFold.folded CompetitorSumWidth.zero
            (contributions entries)).value : ℚ) : ℝ) =
          polynomial.estimatedMean supplier := by
  obtain ⟨receipt, out, hrun, hsteps, htapes, _hheads, hstore, _hvalue⟩ :=
    CompetitorSumEntry.uniform_cold_sum_run recordWidth (contributions entries) hvalid
  exact ⟨receipt, out, hrun, hsteps, htapes, hstore,
    folded_value_eq_estimatedMean supplier recordWidth polynomial entries hcalls hvalid⟩

/-- **The call stream is what the fold reads.**  `Store.source` pins tape `88`
of the fold's exit to the very word stream of AND-four calls that was folded,
so the receipt above cannot be satisfied by a machine that folded something
else. -/
theorem coldFold_source {Atom : Type} {supplier : List Atom → ℚ}
    {recordWidth : ℕ} {polynomial : CircuitPolynomial Atom 4} {entries : List Entry}
    {out : Fin 94 → List Bool}
    (_hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hstore : CompetitorSumFold.Store (foldWidth recordWidth entries)
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (CompetitorSumFold.words (foldWidth recordWidth entries)
        (contributions entries)) out) :
    out 88 = CompetitorSumFold.words (foldWidth recordWidth entries)
      (contributions entries) :=
  hstore.source

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
