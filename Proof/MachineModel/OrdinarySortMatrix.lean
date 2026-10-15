import Proof.MachineModel.OrdinaryLeftMatrix

/-! Actual coordinate sort, paid reset, and selected padded-matrix traversal.
Dimension templates are supplied explicitly and preserved across the sorter. -/
namespace NearCubicWires.RepairOrdinary.SortMatrix
open LocalBitMultitape SupplierPrinter CoordinateKey GridRows LeftPlaneCell
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sortMachine : Machine 11 88 := TapeEmbedding.machine 4 (Rewind.machine SortCarrier.machine)
def matrixMachine : Machine 11 48 :=
  TapeRenaming.machine SortRank.rankLayout (TapeEmbedding.machine 6 MatrixRows.machine)
def machine : Machine 11 136 := Composition.machine sortMachine matrixMachine
def input (req : SortCarrier.Request) (out : List Bool) (used pad rows : ℕ) : Configuration 11 136 :=
  Composition.leftConfig 48 (TapeEmbedding.config ![out.length, 1, 1, 1]
    ![out, UnaryTemplate.tape used, UnaryTemplate.tape pad, UnaryTemplate.tape rows]
    (initialConfiguration (Rewind.machine SortCarrier.machine)
      (Fin.addCases (motive := fun _ : Fin (6 + 1) => List Bool)
        (SourceHandoff.sourceTapes (t := 6) (StablePartition.stream req.records)) (fun _ : Fin 1 => []))))

theorem final_cells {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) : d.tapeCells ≤ space := by
  induction hp with
  | refl c hc => exact hc
  | step _ _ _ _ ih => exact ih

theorem sorted_stream_length (req : SortCarrier.Request) :
    (StablePartition.stream (SortCarrier.sorted req)).length = (StablePartition.stream req.records).length := by
  have hw : ∀ r ∈ SortCarrier.sorted req, (RadixSemantics.word r).length = SortPreparation.width req.records :=
    fun r hr => req.uniform r ((SortCarrier.sorted_perm req).mem_iff.mp hr)
  rw [SortCost.stream_length_of_width _ _ hw, SortCost.stream_length_of_width _ _ req.uniform,
    (SortCarrier.sorted_perm req).length_eq]

theorem joined_run {Rows Columns Used Capacity : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) (left : IntMatrix Rows Used)
    (negative : Bool) (bit : ℕ) (hcap : Used ≤ Capacity)
    (hleft : ∀ row inner, payload (row.castAdd Columns) inner = coefficientBit negative (left row inner) bit)
    (req : SortCarrier.Request) (hgrid : SortCarrier.sorted req = grid I K payload) (out : List Bool) :
    let matrix := WilliamsLoaderForms.rowMajorBitMatrix (fun row inner =>
      coefficientBit negative (padSignedInner (Capacity := Capacity) left row inner) bit)
    let rowCost := (MatrixRows.fields (leftRows I K payload)).length + Rows * (3 * Used + 2 * (Capacity - Used) + 11) + 1
    ∃ r : ExecutionReceipt 11 136,
      runFrom machine (2 * SortCarrier.budget req.records + 3 + rowCost)
        (input req out Used (Capacity - Used) Rows) = some r ∧
      r.final.tapes 7 = out ++ matrix ∧ r.final.heads 7 = (out ++ matrix).length ∧
      r.steps ≤ 2 * SortCarrier.budget req.records + 3 + rowCost ∧
      r.peakTapeCells ≤ 9 * (StablePartition.stream req.records).length + 5 * SortPreparation.width req.records +
        SortCarrier.budget req.records + out.length + (Rows + 3) * Capacity + Rows + 9 := by
  dsimp only
  let rowCost := (MatrixRows.fields (leftRows I K payload)).length + Rows * (3 * Used + 2 * (Capacity - Used) + 11) + 1
  let stored := StablePartition.stream req.records
  let extras := ![out, UnaryTemplate.tape Used, UnaryTemplate.tape (Capacity - Used), UnaryTemplate.tape Rows]
  let heads := ![out.length, 1, 1, 1]
  obtain ⟨source, _, _, hsource, hout, hsteps, hpeak⟩ := Classical.choose_spec (SortCarrier.raw_sort req.records req.uniform)
  have hout' : source.final.tapes 0 = StablePartition.stream (grid I K payload) := by
    change source.final.tapes 0 = StablePartition.stream (SortCarrier.sorted req) at hout
    rw [hgrid] at hout
    exact hout
  obtain ⟨reset, hreset, hresetOut, hresetHeads, hresetSteps, hresetPeak⟩ :=
    Rewind.reset_run SortCarrier.machine (SortCarrier.budget req.records) _ source hsource
  have hfirst := TapeEmbedding.run_embed (Rewind.machine SortCarrier.machine) heads extras _ _ reset hreset
  let first := TapeEmbedding.receipt heads extras reset
  obtain ⟨phase, selected, hselected, hselectedFinal, hselectedSteps, hselectedPeak⟩ :=
    LeftMatrix.selected_run I K payload left negative bit hcap hleft out
  let retained : Fin 6 → List Bool := fun i => reset.final.tapes i.succ
  have he := TapeEmbedding.run_embed MatrixRows.machine (fun _ : Fin 6 => 0) retained _ _ selected hselected
  have hsecond := TapeRenaming.run_rename SortRank.rankLayout (TapeEmbedding.machine 6 MatrixRows.machine) _ _ _ he
  let second := TapeRenaming.receipt SortRank.rankLayout (TapeEmbedding.receipt (fun _ : Fin 6 => 0) retained selected)
  have hmid : Composition.restart first.final matrixMachine.start =
      TapeRenaming.config SortRank.rankLayout (TapeEmbedding.config (fun _ : Fin 6 => 0) retained
        (MatrixRows.config MatrixRows.machine.start (StablePartition.stream (grid I K payload)) 0 out
          Used (Capacity - Used) 1 Rows)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, MatrixRows.config, PaddedRow.config, PayloadCounted.config,
        Fin.addCases, hresetHeads, heads]
    · have hzero := (hresetOut (0 : Fin 6)).trans hout'
      change reset.final.tapes 0 = StablePartition.stream (grid I K payload) at hzero
      funext i
      fin_cases i <;> simp [Composition.restart, first, TapeEmbedding.receipt, TapeEmbedding.config,
        TapeRenaming.config, MatrixRows.config, PaddedRow.config, PayloadCounted.config,
        Fin.addCases, retained, extras, hzero]
  have hnext : runFrom matrixMachine rowCost (Composition.restart first.final matrixMachine.start) = some second := by
    rw [hmid]
    exact hsecond
  have hj := Composition.run_join sortMachine matrixMachine (2 * source.steps + 2) rowCost _ first second hfirst hnext
  have hbound : (2 * source.steps + 2) + 1 + rowCost ≤ 2 * SortCarrier.budget req.records + 3 + rowCost := by omega
  have hmore := runFrom_moreFuel machine ((2 * source.steps + 2) + 1 + rowCost)
    ((2 * SortCarrier.budget req.records + 3 + rowCost) - ((2 * source.steps + 2) + 1 + rowCost)) _ _ hj
  rw [Nat.add_sub_of_le hbound] at hmore
  refine ⟨Composition.joinedReceipt first second, hmore, ?_, ?_, ?_, ?_⟩
  · change (TapeRenaming.config SortRank.rankLayout (TapeEmbedding.config (fun _ : Fin 6 => 0) retained selected.final)).tapes 7 = _
    rw [hselectedFinal]
    simp [TapeRenaming.config, TapeEmbedding.config, MatrixRows.config, PaddedRow.config, PayloadCounted.config, Fin.addCases]
  · change (TapeRenaming.config SortRank.rankLayout (TapeEmbedding.config (fun _ : Fin 6 => 0) retained selected.final)).heads 7 = _
    rw [hselectedFinal]
    simp [TapeRenaming.config, TapeEmbedding.config, MatrixRows.config, PaddedRow.config, PayloadCounted.config, Fin.addCases]
  · change reset.steps + 1 + selected.steps ≤ _
    rw [hresetSteps, hselectedSteps]
    omega
  · change max (reset.peakTapeCells + TapeEmbedding.extraCells extras)
      (selected.peakTapeCells + TapeEmbedding.extraCells retained) ≤ _
    have hdim : Used + (Capacity - Used) = Capacity := Nat.add_sub_of_le hcap
    have hextras : TapeEmbedding.extraCells extras = out.length + Capacity + Rows + 6 := by
      simp [TapeEmbedding.extraCells, extras, Fin.sum_univ_succ]
      omega
    have hfinalCells := final_cells (prefix_of_run _ _ _ _ hreset).1
    have hretained : TapeEmbedding.extraCells retained ≤ reset.peakTapeCells := by
      have hsplit : reset.final.tapeCells = (reset.final.tapes 0).length + TapeEmbedding.extraCells retained := by
        simp [Configuration.tapeCells, TapeEmbedding.extraCells, retained, Fin.sum_univ_succ]
      rw [hsplit] at hfinalCells
      omega
    have hlen : (StablePartition.stream (grid I K payload)).length = stored.length := by
      rw [← hgrid]
      exact sorted_stream_length req
    rw [hlen] at hselectedPeak
    rw [hextras]
    change source.peakTapeCells ≤ 8 * stored.length + 5 * SortPreparation.width req.records + 3 at hpeak
    change max _ _ ≤ 9 * stored.length + 5 * SortPreparation.width req.records +
      SortCarrier.budget req.records + out.length + (Rows + 3) * Capacity + Rows + 9
    simp only [Nat.add_mul] at hselectedPeak ⊢
    omega

end NearCubicWires.RepairOrdinary.SortMatrix
