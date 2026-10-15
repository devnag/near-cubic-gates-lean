import Proof.CaseAnalysis.FinalSupplierTable
import Proof.CaseAnalysis.FinalSupplierRowWriter
import Proof.CaseAnalysis.FinalSupplierWidth
import Proof.CaseAnalysis.FinalSupplierSelect
import Proof.CaseAnalysis.FinalSources
import Proof.CaseAnalysis.RowsEstimatorWholeRetained
import Proof.CaseAnalysis.RowsEstimatorDriverBounds
import Proof.CaseAnalysis.RowsEstimatorLinearBudget
import Proof.CaseAnalysis.RowsPrinterBudget

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients
open NearCubicWires.RepairOrdinary.CompetitorSelectedCount
open NearCubicWires.RepairOrdinary.CompetitorCountMask
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierRowInput

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierExternalRow

noncomputable section

/-! ## 1. The per-row cost, and the hot bucket -/

/-- **The per-external-row cost.**  One object for both duties the consumer has to charge: the
fuel the row is run with (`Whole.budget`) and the steps it actually takes (`Whole.envelope`). -/
def rowEnvelope (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ) : ℕ :=
  Whole.budget a row C Q + Whole.envelope a row C

/-- The coefficient of the hot bucket.  Every summand is a residue of a cited in-cone bound; see
the module header's constant ledger. -/
def rowCoefficient (a : WilliamsAlgorithm) : ℕ :=
  6040042 + 4 * Driver.tableCoefficient a

theorem rowEnvelope_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q s M E : ℕ)
    (hC : (Header.stream row).length ≤ C)
    (hQ : Q ≤ (EquationRow.request row).p)
    (hcuts : row.cuts.length ^ 100 ≤ 2 ^ s)
    (hd : 2 * row.d ≤ s + 1)
    (hM : row.d + row.p + row.cuts.length + C ≤ M)
    (h3 : 3 ≤ E) (he : CompetitorCrossScheduler.exponent a ≤ E) :
    rowEnvelope a row C Q ≤ rowCoefficient a * (2 ^ s * (M + 1) ^ E) := by
  have hp1 : 1 ≤ (2 : ℕ) ^ s := Nat.one_le_pow _ _ (by decide)
  have hp2 : 1 ≤ (M + 1) ^ E := Nat.one_le_pow _ _ (by omega)
  have hpowE : (M + 1) ^ 3 ≤ (M + 1) ^ E := Nat.pow_le_pow_right (by omega) h3
  have hone : (M + 1) ≤ (M + 1) ^ E :=
    le_trans (Nat.le_self_pow (by omega) _) (Nat.pow_le_pow_right (by omega) h3)
  have hsq : (M + 1) ^ 2 ≤ (M + 1) ^ E := Nat.pow_le_pow_right (by omega) (by omega)
  set Y : ℕ := 2 ^ s * (M + 1) ^ E with hYdef
  have hYbig : (M + 1) ^ E ≤ Y := Nat.le_mul_of_pos_left _ (by omega)
  have hY1 : 1 ≤ Y := le_trans hp2 hYbig
  -- the linear fuel of the row
  have hb := CloseoutRowsEstimator.whole_linear a row C Q hC hQ
  unfold CloseoutRowsEstimator.linearFuel at hb
  -- the step envelope of the row, unfolded to its four summands
  have henv : Whole.envelope a row C = 10000 * (Cold.scale row C) ^ 2 + 1 +
      (EquationRowFramed.uniformBudget row + 1 +
        CompetitorCountTableRecord.envelope a (EquationRow.request row)) := rfl
  -- the polynomial pieces
  have hmass : EquationRowRaw.mass row ≤ M + 1 := by
    unfold EquationRowRaw.mass; omega
  have hmass3 : (EquationRowRaw.mass row) ^ 3 ≤ Y :=
    le_trans (le_trans (Nat.pow_le_pow_left hmass 3) hpowE) hYbig
  have hscale : Cold.scale row C ≤ 2 * (M + 1) := by
    unfold Cold.scale; omega
  have hscale2 : (Cold.scale row C) ^ 2 ≤ 4 * Y := by
    calc (Cold.scale row C) ^ 2 ≤ (2 * (M + 1)) ^ 2 := Nat.pow_le_pow_left hscale 2
      _ = 4 * (M + 1) ^ 2 := by ring
      _ ≤ 4 * Y := Nat.mul_le_mul_left 4 (le_trans hsq hYbig)
  have hCY : C ≤ Y := le_trans (by omega) (le_trans hone hYbig)
  have hub : EquationRowFramed.uniformBudget row ≤ 5000000 * Y := by
    refine le_trans (CloseoutRowsPrinterBudget.printer_linear_table s row hcuts) ?_
    have hdp : (row.d + row.p + 1) ^ 3 ≤ (M + 1) ^ E :=
      le_trans (Nat.pow_le_pow_left (by omega) 3) hpowE
    calc 5000000 * 2 ^ s * (row.d + row.p + 1) ^ 3
        = 5000000 * (2 ^ s * (row.d + row.p + 1) ^ 3) := by ring
      _ ≤ 5000000 * (2 ^ s * (M + 1) ^ E) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdp)
  -- the ONE table factor, charged twice
  have htab : CompetitorCountTableRecord.envelope a (EquationRow.request row)
      ≤ 2 * (Driver.tableCoefficient a * Y) := by
    refine le_trans (Driver.table_bound a row) ?_
    unfold Driver.tableValue
    have h1 : (2 ^ row.d) ^ 2 ≤ 2 * 2 ^ s := by
      rw [← pow_mul]
      calc (2 : ℕ) ^ (row.d * 2) ≤ 2 ^ (s + 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 * 2 ^ s := by rw [pow_succ]; ring
    have h2 : (row.d + row.p + 1) ^ CompetitorCrossScheduler.exponent a ≤ (M + 1) ^ E :=
      le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) he)
    calc Driver.tableCoefficient a * (2 ^ row.d) ^ 2
            * (row.d + row.p + 1) ^ CompetitorCrossScheduler.exponent a
        ≤ Driver.tableCoefficient a * (2 * 2 ^ s) * ((M + 1) ^ E) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 2 * (Driver.tableCoefficient a * (2 ^ s * (M + 1) ^ E)) := by ring
  -- assemble: linear in the two atoms `Y` and `Driver.tableCoefficient a * Y`
  have hsplit : rowCoefficient a * Y
      = 6040042 * Y + 4 * (Driver.tableCoefficient a * Y) := by
    unfold rowCoefficient; ring
  rw [hsplit]
  unfold rowEnvelope
  rw [henv]
  omega

end

/-! ## 2. The external row: `WholeRetained.run` at the C10 supplier request -/

noncomputable section

variable {n : ℕ} (a : DecompositionAlgorithm) (live : Finset (Fin n))
  (occ : List (SupportedNormalizedGate n)) (s : ℕ)
  (harity : (s + 1) / 2 + s / 2 = liveᶜ.card) (P : StructuralGF2Polynomial) (w : ℕ)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2 ^ w)
  (hpos : 1 ≤ w) (hload : 200 * (live.card + w * (live.card + 2)) ≤ s)

/-- The residual half-width of the supplier row is `(s+1)/2` (`CloseoutRows.commonInput`,
`Proof/CaseAnalysis/RowsCommonInput.lean`), so the single table factor `(2 ^ d) ^ 2` is at most
`2 * 2 ^ s` — the `2 ^ (q-K)` of `paper.tex:2783-2785`. -/
theorem rowInput_d :
    (rowInput a live occ s harity P w hs hmon hpos hload).d = (s + 1) / 2 := rfl

/-- The printed cut stream obeys the `s_gen` size gate (`paper.tex:2885`), which is exactly
`C10SupplierRowInput.gate` transported along `rowInput_cuts`. -/
theorem rowInput_cuts_gate :
    (rowInput a live occ s harity P w hs hmon hpos hload).cuts.length ^ 100 ≤ 2 ^ s := by
  have h := gate a live occ s harity P w hmon hpos hload
  rw [batch_length_eq (pool a live occ s harity) (live.card + 1) w
    (bank a live occ s harity P) (bank_rows_le a live occ s harity P w hmon)] at h
  rw [rowInput_cuts a live occ s harity P w hs hmon hpos hload]
  exact h

theorem externalRow_run (sources : EightSources) (C : ℕ)
    (hcap : ExtIncidence.NativeOutputBound.allowance
        (ExtIncidence.NativeMeasured.capacity (pool a live occ s harity) (live.card + 1) w)
        (live.card + 1) (2 ^ live.card) ≤ C)
    (est : CompetitorValidity.Estimate) (arity scale : ℕ)
    (select :
      Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U →
        Fin (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload)).U → Bool) :
    ∃ actual,
      runFrom (Whole.machine (williamsOf sources))
          (Whole.budget (williamsOf sources)
            (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1))
          (Whole.entry (williamsOf sources)
            (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1) est
            (C10SupplierWidth.denominator arity scale) select) = some actual ∧
      Whole.budget (williamsOf sources)
          (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1)
          + actual.steps ≤
        rowEnvelope (williamsOf sources)
          (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1) ∧
      actual.final.tapes (Whole.recordSlot (producer (williamsOf sources))) =
        Stream.recordWord
          (scalarWidth (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload))
            (live.card + 1)) est
          (selected (CompetitorSelectedCells.cells
            (rowInput a live occ s harity P w hs hmon hpos hload).odd
            (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select)).sum
          (C10SupplierWidth.denominator arity scale) ∧
      actual.final.heads (Whole.recordSlot (producer (williamsOf sources))) =
        (Stream.recordWord
          (scalarWidth (EquationRow.request (rowInput a live occ s harity P w hs hmon hpos hload))
            (live.card + 1)) est
          (selected (CompetitorSelectedCells.cells
            (rowInput a live occ s harity P w hs hmon hpos hload).odd
            (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select)).sum
          (C10SupplierWidth.denominator arity scale)).length ∧
      actual.final.tapes (Whole.matrixSlot (producer (williamsOf sources))) =
        physicalInput (EquationRow.request
          (rowInput a live occ s harity P w hs hmon hpos hload)) ∧
      actual.final.heads ((52 : Fin 70).castAdd
        (CloseoutRowsRawRecord.tapes (producer (williamsOf sources)))) = 0 ∧
      actual.final.tapes ((68 : Fin 70).castAdd
        (CloseoutRowsRawRecord.tapes (producer (williamsOf sources)))) =
        List.replicate C true := by
  have hC : (Header.stream (rowInput a live occ s harity P w hs hmon hpos hload)).length ≤ C :=
    le_trans (C10SupplierRowWriter.headerStream_le_pow a live occ s harity P w hs hmon hpos hload)
      hcap
  obtain ⟨actual, hrun, hsteps, hrec, hhead, hmat, h52, h68⟩ :=
    WholeRetained.run (williamsOf sources)
      (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1) est
      (C10SupplierWidth.denominator arity scale)
      (C10SupplierTable.table a live occ s harity P w hs hmon hpos hload) select hC
      (rowInput_p a live occ s harity P w hs hmon hpos hload)
      (C10SupplierTable.table_lt a live occ s harity P w hs hmon hpos hload)
      (fun i => C10SupplierTable.table_modEq a live occ s harity P w hs hmon hpos hload
        i.divNat i.modNat)
  refine ⟨actual, hrun, ?_, hrec, hhead, hmat, h52, h68⟩
  unfold rowEnvelope
  omega

theorem externalRow_envelope_le (sources : EightSources) (C M E : ℕ)
    (hcap : ExtIncidence.NativeOutputBound.allowance
        (ExtIncidence.NativeMeasured.capacity (pool a live occ s harity) (live.card + 1) w)
        (live.card + 1) (2 ^ live.card) ≤ C)
    (hM : (rowInput a live occ s harity P w hs hmon hpos hload).d
        + (rowInput a live occ s harity P w hs hmon hpos hload).p
        + (rowInput a live occ s harity P w hs hmon hpos hload).cuts.length + C ≤ M)
    (h3 : 3 ≤ E)
    (he : CompetitorCrossScheduler.exponent (williamsOf sources) ≤ E) :
    rowEnvelope (williamsOf sources)
        (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1)
      ≤ rowCoefficient (williamsOf sources) * (2 ^ s * (M + 1) ^ E) := by
  have hC : (Header.stream (rowInput a live occ s harity P w hs hmon hpos hload)).length ≤ C :=
    le_trans (C10SupplierRowWriter.headerStream_le_pow a live occ s harity P w hs hmon hpos hload)
      hcap
  have hd : 2 * (rowInput a live occ s harity P w hs hmon hpos hload).d ≤ s + 1 := by
    rw [rowInput_d a live occ s harity P w hs hmon hpos hload]
    omega
  exact rowEnvelope_le (williamsOf sources)
    (rowInput a live occ s harity P w hs hmon hpos hload) C (live.card + 1) s M E hC
    (rowInput_p a live occ s harity P w hs hmon hpos hload)
    (rowInput_cuts_gate a live occ s harity P w hs hmon hpos hload) hd hM h3 he

end

noncomputable section

variable (request : FourfoldRequest NormalizedSymmetricThresholdCircuit) (liveScale : ℕ)
  (a : DecompositionAlgorithm) (s : ℕ)
  (harity : (s + 1) / 2 + s / 2 = (liveSet request liveScale)ᶜ.card)
  (P : StructuralGF2Polynomial) (w : ℕ) (hs : 67 ≤ s)
  (hmon : (CloseoutRowsUniversal.lower a (liveSet request liveScale)
    (symmetricFourfoldOccurrences request) P).length < 2 ^ w)
  (hpos : 1 ≤ w)
  (hload : 200 * ((liveSet request liveScale).card +
    w * ((liveSet request liveScale).card + 2)) ≤ s)

theorem externalRow_run_offsetSelect (sources : EightSources) (C : ℕ)
    (hcap : ExtIncidence.NativeOutputBound.allowance
        (ExtIncidence.NativeMeasured.capacity
          (pool a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity)
          ((liveSet request liveScale).card + 1) w)
        ((liveSet request liveScale).card + 1)
        (2 ^ (liveSet request liveScale).card) ≤ C)
    (est : CompetitorValidity.Estimate) (arity scale : ℕ)
    (f : Fin request.circuits.length → ℕ) :
    ∃ actual,
      runFrom (Whole.machine (williamsOf sources))
          (Whole.budget (williamsOf sources)
            (rowInput a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
              P w hs hmon hpos hload) C ((liveSet request liveScale).card + 1))
          (Whole.entry (williamsOf sources)
            (rowInput a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
              P w hs hmon hpos hload) C ((liveSet request liveScale).card + 1) est
            (C10SupplierWidth.denominator arity scale)
            (C10SupplierSelect.offsetSelect request liveScale f)) = some actual ∧
      Whole.budget (williamsOf sources)
          (rowInput a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
            P w hs hmon hpos hload) C ((liveSet request liveScale).card + 1)
          + actual.steps ≤
        rowEnvelope (williamsOf sources)
          (rowInput a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
            P w hs hmon hpos hload) C ((liveSet request liveScale).card + 1) ∧
      actual.final.tapes (Whole.recordSlot (producer (williamsOf sources))) =
        Stream.recordWord
          (scalarWidth (EquationRow.request
            (rowInput a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
              P w hs hmon hpos hload)) ((liveSet request liveScale).card + 1)) est
          (selected (CompetitorSelectedCells.cells
            (rowInput a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
              P w hs hmon hpos hload).odd
            (C10SupplierTable.table a (liveSet request liveScale)
              (symmetricFourfoldOccurrences request) s harity P w hs hmon hpos hload)
            (C10SupplierSelect.offsetSelect request liveScale f))).sum
          (C10SupplierWidth.denominator arity scale) := by
  obtain ⟨actual, hrun, hsteps, hrec, _, _, _, _⟩ :=
    externalRow_run a (liveSet request liveScale) (symmetricFourfoldOccurrences request) s harity
      P w hs hmon hpos hload sources C hcap est arity scale
      (C10SupplierSelect.offsetSelect request liveScale f)
  exact ⟨actual, hrun, hsteps, hrec⟩

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierExternalRow
