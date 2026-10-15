import Proof.MachineModel.ScannerBare
import Proof.CaseAnalysis.RowsEstimatorPrepareLive
import Proof.CaseAnalysis.RowsEstimatorPreparedPorts
import Proof.CaseAnalysis.FinalRowCommonCapacity

/-! A reused, common-capacity row transaction: copy the seven produced fields,
then execute the actual warm printer, append and reset. The native header can
remain padded to C throughout. Field production and the scanner remain explicit
upstream work; this theorem does not assume that an arbitrary scratch bank
contains either. -/
namespace NearCubicWires.P1Independent.WarmTransaction
open LocalBitMultitape RepairRepresentation RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open RepairOrdinary.MatrixScoreBatch
open RepairOrdinary.CompetitorSelectedCount RepairOrdinary.CompetitorCountMask
open RepairOrdinary.CloseoutRowsEstimatorCoefficients
open RepairOrdinary.CompetitorCrossScheduler (producer)
open RepairSource.CloseoutFinal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

attribute [local irreducible] Warm.machine Warm.input WarmFields.words
  CompetitorCrossScheduler.producer

noncomputable def machine (a : WilliamsAlgorithm) :=
  Composition.machine (WarmPrepare.copy (producer a))
    (TapeEmbedding.machine 7 (WarmActual.machine a))

def caps (p : Program) (C : ℕ) (i : Fin (WarmPrepare.tapes p)) : ℕ :=
  if i.val=52 then C else 0

noncomputable def input (p : Program) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) : Fin (WarmPrepare.tapes p) → List Bool :=
  fun i => ZeroPadding.pad (caps p C i)
    (WarmPrepare.live p (WarmPrepare.data p
      (WarmReuse.padded p D (WarmFields.bare p row C)) D (D+1)
      (WarmFields.words row Q q den select)) out i)

noncomputable def output (p : Program) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) : Fin (WarmPrepare.tapes p) → List Bool :=
  fun i => ZeroPadding.pad (caps p C i)
    (Fin.addCases (motive:=fun _ => List Bool)
      (exitTapes p D (Warm.input p row C Q q den select) out)
      (WarmFields.words row Q q den select) i)

/-- The copier starts at precisely the scanner's complete padded bare bank,
extended by the seven produced metadata words. No fresh log is required. -/
theorem input_eq (p : Program) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) :
    input p row C D Q q den select out =
      Fin.addCases (m:=Reuse.tapes p) (n:=7) (motive:=fun _ => List Bool)
        (ScannerBare.bareBank p row C D out) (WarmFields.words row Q q den select) := by
  unfold input
  rw [← WarmPrepared.live_data]
  funext i
  have hT := tapes_ge p
  refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left]
    refine Fin.addCases (m:=WholePrefix.tapes p+1) (n:=2) (fun k => ?_) (fun k => ?_) j
    · refine Fin.addCases (m:=WholePrefix.tapes p) (n:=1) (fun l => ?_) (fun l => ?_) k
      · simp only [Fin.addCases_left,ScannerBare.bareBank,ScannerBare.paddedBare,caps,Fin.val_castAdd]
        rfl
      · have hne : WholePrefix.tapes p+l.val ≠ 52 := by omega
        simp only [ScannerBare.bareBank,Fin.addCases_left,Fin.addCases_right,caps,
          Fin.val_castAdd,Fin.val_natAdd,hne,if_false,ZeroPadding.pad_zero]
    · have hne : WholePrefix.tapes p+1+k.val ≠ 52 := by omega
      simp only [ScannerBare.bareBank,Fin.addCases_right,caps,
        Fin.val_castAdd,Fin.val_natAdd,hne,if_false,ZeroPadding.pad_zero]
  · have hne : Reuse.tapes p+j.val ≠ 52 := by unfold Reuse.tapes;omega
    simp only [Fin.addCases_right,caps,Fin.val_natAdd,hne,if_false,ZeroPadding.pad_zero]

theorem copy_run (p : Program) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) (hd : ∀ i,(WarmFields.words row Q q den select i).length ≤ D) :
    Step (WarmPrepare.copy p) (2*D+4) (WarmPrepare.heads p out)
      (WarmPrepare.live p (WarmPrepare.data p (WarmReuse.padded p D (WarmFields.bare p row C))
        D (D+1) (WarmFields.words row Q q den select)) out)
      (WarmPrepare.heads p out)
      (WarmPrepare.live p (WarmPrepare.data p (WarmReuse.padded p D (Warm.input p row C Q q den select))
        D (D+1) (WarmFields.words row Q q den select)) out) := by
  obtain ⟨r,hr,rh,rt,_⟩ := WarmPrepare.copy_live p
    (WarmReuse.padded p D (WarmFields.bare p row C)) D (WarmFields.words row Q q den select) out
    (WarmFields.padded_field p row C D) hd
  rw [WarmFields.padded_installed] at rt
  exact Step.of_run hr rh rt

theorem entry_heads (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) :
    Fin.addCases (motive:=fun _ => ℕ)
      (C10RowCommonCapacity.entry a row C Q D q den select out).heads (fun _ : Fin 7 => 0) =
      WarmPrepare.heads (producer a) out := by
  change Fin.addCases (m:=Reuse.tapes (producer a)) (n:=7) (motive:=fun _ => ℕ)
    (Fin.addCases (m:=WholePrefix.tapes (producer a)+1) (n:=2) (motive:=fun _ => ℕ)
    (fun _ : Fin (WholePrefix.tapes (producer a)+1) => 0)
    (![out.length,0] : Fin 2 → ℕ)) (fun _ : Fin 7 => 0) = _
  exact WarmPrepared.live_heads (producer a) out

theorem entry_tapes (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) :
    Fin.addCases (motive:=fun _ => List Bool)
      (C10RowCommonCapacity.entry a row C Q D q den select out).tapes (WarmFields.words row Q q den select) =
      WarmPrepare.live (producer a) (WarmPrepare.data (producer a)
        (WarmReuse.padded (producer a) D (Warm.input (producer a) row C Q q den select))
        D (D+1) (WarmFields.words row Q q den select)) out := by
  rw [C10RowCommonCapacity.entry, C10RowFrameJoin.entry_tapes_fun]
  exact WarmPrepared.live_data (producer a) _ D (D+1) _ out

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (den : ℕ)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D) :
    let word := Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
      (selected (CompetitorSelectedCells.cells row.odd f select)).sum den
    Step (machine a) (2*D+4+1+C10RowCommonCapacity.budget a row Q D)
      (WarmPrepare.heads (producer a) out)
      (input (producer a) row C D Q q den select out)
      (Fin.addCases (motive:=fun _ => ℕ)
        (bankHeads (producer a) (out++word)) (fun _ : Fin 7 => 0))
      (output (producer a) row C D Q q den select (out++word)) := by
  dsimp only
  let p := producer a
  let fields := WarmFields.words row Q q den select
  have hd : ∀ i,(fields i).length ≤ D :=
    fun i => (WarmFields.bounded a row C Q q den select hC hQ i).trans hD
  have cp := copy_run p row C D Q q den select out hd
  have warm := (C10RowCommonCapacity.bank_step a row C Q D q den f select out
    hC hQ hf hc hD).embed (fun _ : Fin 7 => 0) fields
  have warm' := warm.congr_in (entry_heads a row C D Q q den select out)
    (entry_tapes a row C D Q q den select out)
  exact (cp.seq warm').pad (caps p C)

theorem budget_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D) :
    2*D+4+1+C10RowCommonCapacity.budget a row Q D ≤ 8*D+74 := by
  have hf := (Driver.fuel_bound a row C Q hC hQ).trans hD
  have hw := Warm.split_budget a row C Q
  have hb := (Driver.append_bound a row C Q hQ).trans (Nat.add_le_add_right hD 1)
  unfold C10RowCommonCapacity.budget Reuse.budget Reuse.afterBudget
  omega

end NearCubicWires.P1Independent.WarmTransaction
