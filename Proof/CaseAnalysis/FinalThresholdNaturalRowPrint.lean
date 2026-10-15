import Proof.CaseAnalysis.FinalThresholdNaturalSum
import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.CaseAnalysis.FinalRowFrameJoin

/-!
A.13.7/A.13.10: separate fixed-scalar (g,p,e,f) rows, selected at residual z.
This identifies the ordinary printer's table and exact selected row payload.
The outer g sum is natural addition; no |G| enters the denominator or a row.
Physical row preparation, the bounded family reload, and resource envelopes
remain the explicit premises of the existing ordinary printer/loop donors.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrinter NearCubicWires.SupplierPrime
open NearCubicWires.SupplierRadix NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.RepairOrdinary.CompetitorCountMask (selected)
open NearCubicWires.RepairOrdinary.MatrixScoreBatch
open scoped BigOperators

namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalRowPrint
open C10ThresholdParityRow C10ThresholdNaturalSum C10ExternalRowLoop C10SupplierRowInput
noncomputable section

variable (a : DecompositionAlgorithm)
  (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

theorem thrOffset_lt (liveScale : ℕ)
    (z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    (sel : ThresholdRows.Selection a r) {cutoff : ℕ} (prime : PrimeIndex cutoff) :
    thrOffset a r liveScale z sel prime.val < prime.val := by
  have hp : (0 : ℤ) < prime.val := by
    exact_mod_cast (mem_primesUpTo.mp prime.property).1.pos
  unfold thrOffset modularResidualOffset
  exact (Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hp))).mpr
    (Int.emod_lt_of_pos _ hp)

def scalarRowValue (liveScale listDen : ℕ) {cutoff : ℕ}
    (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen)
    (offset : Fin prime.val) : ℕ :=
  ∑ z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card,
    if thrOffset a r liveScale z sel prime.val = offset.val then
      exactColumnCount (thrHolds r liveScale)
        (thresholdRow a r sel liveScale listDen prime.val offset.val seed) z
    else 0

theorem sum_scalarRowValue (liveScale listDen : ℕ) {cutoff : ℕ}
    (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen) :
    (∑ offset : Fin prime.val, scalarRowValue a r liveScale listDen sel prime seed offset) =
      ∑ z : BitInput (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card,
        exactColumnCount (thrHolds r liveScale)
          (thresholdRow a r sel liveScale listDen prime.val
            (thrOffset a r liveScale z sel prime.val) seed) z := by
  unfold scalarRowValue
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  let chosen : Fin prime.val := ⟨thrOffset a r liveScale z sel prime.val,
    thrOffset_lt a r liveScale z sel prime⟩
  rw [Finset.sum_eq_single chosen]
  · simp [chosen]
  · intro offset _ hne
    apply if_neg
    intro heq
    apply hne
    exact Fin.ext heq.symm
  · simp

theorem nativeNumerator_eq_fixedScalarSum (liveScale listDen cutoff : ℕ) :
    nativeNumerator a r liveScale listDen cutoff =
      ∑ sel : ThresholdRows.Selection a r, ∑ prime : PrimeIndex cutoff,
        ∑ seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen,
          ∑ offset : Fin prime.val, scalarRowValue a r liveScale listDen sel prime seed offset := by
  rw [nativeNumerator_eq_tableSum]
  apply Finset.sum_congr rfl
  intro sel _
  apply Finset.sum_congr rfl
  intro prime _
  apply Finset.sum_congr rfl
  intro seed _
  exact (sum_scalarRowValue a r liveScale listDen sel prime seed).symm

section Table
variable (liveScale s : ℕ)
  (harity : (s + 1) / 2 + s / 2 =
    (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
  (P : StructuralGF2Polynomial) (w : ℕ) (hs : 67 ≤ s)
  (hmon : (CloseoutRowsUniversal.lower a
    (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
    (thresholdFourfoldOccurrences r) P).length < 2 ^ w)
  (hpos : 1 ≤ w)
  (hload : 200 * ((normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card +
    w * ((normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card + 2)) ≤ s)

theorem table_eq_thresholdCount
    (i j : Fin (EquationRow.request (rowInput a
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
      (thresholdFourfoldOccurrences r) s harity P w hs hmon hpos hload)).U) :
    C10SupplierTable.table a (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
        (thresholdFourfoldOccurrences r) s harity P w hs hmon hpos hload i j =
      exactColumnCount (thrHolds r liveScale) P
        (printerPoint (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
          s harity i.val j.val) :=
  C10SupplierTable.table_eq_exactColumnCount a
    (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
    (thresholdFourfoldOccurrences r) s harity P w hs hmon hpos hload i j

end Table

theorem selected_sum_printerPoint {q : ℕ} (live : Finset (Fin q)) (s : ℕ)
    (harity : (s + 1) / 2 + s / 2 = liveᶜ.card) (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ ((s + 1) / 2)) (hodd : odd = decide (s % 2 = 1))
    (payload : BitInput liveᶜ.card → ℕ) (keep : BitInput liveᶜ.card → Bool)
    (table : Fin u → Fin u → ℕ)
    (htable : ∀ i j, table i j = payload (printerPoint live s harity i.val j.val)) :
    (selected (CompetitorSelectedCells.cells odd table
      (fun i j => keep (printerPoint live s harity i.val j.val)))).sum =
      ∑ z : BitInput liveᶜ.card, if keep z then payload z else 0 := by
  have hR := harity_right live s harity
  have hL := harity_left live s harity
  have hcard := harity_card live s harity
  have hfun : (fun i j : Fin u =>
      if keep (printerPoint live s harity i.val j.val) = true then table i j else 0) =
    fun i j : Fin u =>
      (fun a b : ℕ => if keep (printerPoint live s harity a b) then
        payload (printerPoint live s harity a b) else 0) i.val j.val := by
    funext i j
    rw [htable i j]
  rw [RowExternalSelection.cells_selected_sum, hfun,
    C10SupplierSelect.total_eq_sum_half live
      (fun a b : ℕ => if keep (printerPoint live s harity a b) then
        payload (printerPoint live s harity a b) else 0)
      u odd (by rw [hu, hR]) (by rw [hodd, hcard])]
  exact sum_printerPoint live s harity _ _ hR.symm hL.symm
    (fun z => if keep z then payload z else 0)

theorem selected_sum_eq_scalarRowValue (liveScale listDen s : ℕ)
    (harity : (s + 1) / 2 + s / 2 =
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    {cutoff : ℕ} (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen)
    (offset : Fin prime.val) (u : ℕ) (odd : Bool)
    (hu : u = 2 ^ ((s + 1) / 2)) (hodd : odd = decide (s % 2 = 1))
    (table : Fin u → Fin u → ℕ)
    (htable : ∀ i j, table i j =
      exactColumnCount (thrHolds r liveScale)
        (thresholdRow a r sel liveScale listDen prime.val offset.val seed)
        (printerPoint (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
          s harity i.val j.val)) :
    (selected (CompetitorSelectedCells.cells odd table
      (fun i j => decide (thrOffset a r liveScale
        (printerPoint (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
          s harity i.val j.val) sel prime.val = offset.val)))).sum =
      scalarRowValue a r liveScale listDen sel prime seed offset := by
  simpa only [scalarRowValue, decide_eq_true_eq] using
    selected_sum_printerPoint
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale) s harity u odd hu hodd
      (exactColumnCount (thrHolds r liveScale)
        (thresholdRow a r sel liveScale listDen prime.val offset.val seed))
      (fun z => decide (thrOffset a r liveScale z sel prime.val = offset.val)) table htable

/-- The existing ordinary printer appends the actual fixed-scalar payload at
the caller's denominator. In particular the caller may supply nativeDenominator.
The input bank/header capacity and per-row load remain explicit. -/
theorem fixed_scalar_bank_step (printer : WilliamsAlgorithm) (liveScale listDen s : ℕ)
    (harity : (s + 1) / 2 + s / 2 =
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)ᶜ.card)
    {cutoff : ℕ} (sel : ThresholdRows.Selection a r) (prime : PrimeIndex cutoff)
    (seed : NormalizedOccurrenceListSeed (thresholdFourfoldOccurrences r) liveScale listDen)
    (offset : Fin prime.val) (w : ℕ) (hs : 67 ≤ s)
    (hmon : (CloseoutRowsUniversal.lower a
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
      (thresholdFourfoldOccurrences r)
      (thresholdRow a r sel liveScale listDen prime.val offset.val seed)).length < 2 ^ w)
    (hpos : 1 ≤ w)
    (hload : 200 * ((normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card +
      w * ((normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale).card + 2)) ≤ s)
    (C : ℕ) (est : CompetitorValidity.Estimate) (den : ℕ) (out : List Bool)
    (hC : (CloseoutRowsEstimator.Header.stream (rowInput a
      (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
      (thresholdFourfoldOccurrences r) s harity
      (thresholdRow a r sel liveScale listDen prime.val offset.val seed)
      w hs hmon hpos hload)).length ≤ C) :
    let live := normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale
    let row := rowInput a live (thresholdFourfoldOccurrences r) s harity
      (thresholdRow a r sel liveScale listDen prime.val offset.val seed) w hs hmon hpos hload
    let select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool :=
      fun i j => decide (thrOffset a r liveScale
        (printerPoint live s harity i.val j.val) sel prime.val = offset.val)
    let word := CloseoutRowsEstimatorCoefficients.Stream.recordWord
      (CompetitorSelectedCount.scalarWidth (EquationRow.request row) (live.card + 1))
      est (scalarRowValue a r liveScale listDen sel prime seed offset) den
    ExtDecompositionBatch.Step (CloseoutRowsEstimator.WarmActual.machine printer)
      (CloseoutRowsEstimator.WarmActual.budget printer row C (live.card + 1))
      (CloseoutRowsEstimator.WarmActual.entry printer row C (live.card + 1) est den select out).heads
      (CloseoutRowsEstimator.WarmActual.entry printer row C (live.card + 1) est den select out).tapes
      (C10RowFrameJoin.bankHeads (CompetitorCrossScheduler.producer printer) (out ++ word))
      (C10RowFrameJoin.exitTapes (CompetitorCrossScheduler.producer printer)
        (CloseoutRowsEstimator.Driver.value printer row.d row.p row.cuts.length C)
        (CloseoutRowsEstimator.Warm.input (CompetitorCrossScheduler.producer printer)
          row C (live.card + 1) est den select) (out ++ word)) := by
  dsimp only
  have hrun := C10RowFrameJoin.bank_row_step printer _ C _ est den
    (C10SupplierTable.table a _ _ s harity _ w hs hmon hpos hload)
    (fun i j => decide (thrOffset a r liveScale
      (printerPoint (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
        s harity i.val j.val) sel prime.val = offset.val)) out hC
    (rowInput_p a _ _ s harity _ w hs hmon hpos hload)
    (C10SupplierTable.table_lt a _ _ s harity _ w hs hmon hpos hload)
    (fun i => C10SupplierTable.table_modEq a _ _ s harity _ w hs hmon hpos hload
      i.divNat i.modNat)
  have hselected := selected_sum_eq_scalarRowValue a r liveScale listDen s harity sel prime seed
    offset (EquationRow.request
      (rowInput a (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
        (thresholdFourfoldOccurrences r) s harity
        (thresholdRow a r sel liveScale listDen prime.val offset.val seed) w hs hmon hpos hload)).U
    (rowInput a (normalizedLiveSet (thresholdFourfoldOccurrences r) liveScale)
      (thresholdFourfoldOccurrences r) s harity
      (thresholdRow a r sel liveScale listDen prime.val offset.val seed) w hs hmon hpos hload).odd
    rfl rfl _ (table_eq_thresholdCount a r liveScale s harity _ w hs hmon hpos hload)
  rw [hselected] at hrun
  exact hrun

end
end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdNaturalRowPrint
