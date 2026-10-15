import Proof.CaseAnalysis.FinalWorkerFold

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairSource.VerifierDecoding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The scalar width at which the multiply stage and the fold agree: the fold's
own uniform prefix width for `entries.length` records of scalar width
`CompetitorRationalDecision.width recordWidth`. -/
def joinWidth (recordWidth : ℕ) (entries : List Entry) : ℕ :=
  foldWidth (CompetitorRationalDecision.width recordWidth) entries

theorem contributions_length (entries : List Entry) :
    (contributions entries).length = entries.length := by
  rw [contributions, List.length_map]

/-- The multiply stage's scalar width fits inside the join width. -/
theorem width_le_joinWidth (recordWidth : ℕ) (entries : List Entry) :
    CompetitorRationalDecision.width recordWidth ≤ joinWidth recordWidth entries := by
  unfold joinWidth foldWidth CompetitorSumWidth.width
  nlinarith [Nat.zero_le (contributions entries).length,
    Nat.zero_le (CompetitorRationalDecision.width recordWidth)]

/-- One call per record fits inside the join width. -/
theorem length_le_joinWidth (recordWidth : ℕ) (entries : List Entry) :
    entries.length ≤ joinWidth recordWidth entries := by
  unfold joinWidth foldWidth CompetitorSumWidth.width
  rw [contributions_length]
  nlinarith [Nat.zero_le entries.length,
    Nat.zero_le (CompetitorRationalDecision.width recordWidth)]

/-- **C.10.1, both stages.**  At the join width, the multiply stage consumes the
AND-four call records and emits, on port `74`, exactly the term stream the cold
fold reads; the fold then stores an estimate whose value is the paper's
`mu~ = polynomial.estimatedMean supplier`.  The unary driver on port `88` has
one cell per supplier call. -/
theorem callStream_folds_to_estimatedMean {Atom : Type} (supplier : List Atom → ℚ)
    (recordWidth : ℕ) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid recordWidth entry) :
    ∃ stream,
      ClockJoin.ReadyRun CompetitorMonomialEntry.machine
          (CompetitorMonomialEntry.readyBudget (joinWidth recordWidth entries)
            entries.length)
          (CloseoutRowsEstimatorCoefficients.EntryMachine.readyInput recordWidth
            (joinWidth recordWidth entries) entries) stream ∧
        stream 74 = CompetitorSumFold.words (joinWidth recordWidth entries)
          (contributions entries) ∧
        stream 88 = CompareMachine.word entries.length ∧
        ∃ receipt out,
          run CompetitorSumEntry.machine
              (CompetitorSumEntry.budget (joinWidth recordWidth entries)
                (contributions entries).length)
              (CompetitorSumEntry.input (joinWidth recordWidth entries)
                (contributions entries)) = some receipt ∧
            receipt.steps ≤ CompetitorSumEntry.budget (joinWidth recordWidth entries)
              (contributions entries).length ∧
            (∀ i : Fin 94, receipt.final.tapes (i.castAdd 1) = out i) ∧
            CompetitorSumFold.Store (joinWidth recordWidth entries)
              (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
              (CompetitorSumFold.words (joinWidth recordWidth entries)
                (contributions entries)) out ∧
            (((CompetitorSumFold.folded CompetitorSumWidth.zero
                (contributions entries)).value : ℚ) : ℝ) =
              polynomial.estimatedMean supplier := by
  obtain ⟨stream, hready, hterm, _hshort, hdriver, hvalid⟩ :=
    CloseoutRowsEstimatorCoefficients.EntryMachine.ready_stream_run recordWidth
      (joinWidth recordWidth entries) entries hentries
      (width_le_joinWidth recordWidth entries) (length_le_joinWidth recordWidth entries)
  obtain ⟨receipt, out, hrun, hsteps, htapes, hstore, hvalue⟩ :=
    coldFold_estimatedMean supplier (CompetitorRationalDecision.width recordWidth)
      polynomial entries hcalls hvalid
  exact ⟨stream, hready, hterm, hdriver, receipt, out, hrun, hsteps, htapes, hstore, hvalue⟩

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
