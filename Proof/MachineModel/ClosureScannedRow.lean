import Proof.MachineModel.Transaction

/-! Paper A.3/C.10: one paid scanner, metadata copy, native row computation,
record append and reset, at one common capacity. The inputs are the produced
header, three scanner fields and seven estimator fields. No answer stream is
an input. The complete exit bank is retained for the next row's producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ScannedRow
open LocalBitMultitape RepairRepresentation RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open RepairOrdinary.RecoveryRootRound RepairOrdinary.MatrixScoreBatch
open RepairOrdinary.CompetitorSelectedCount RepairOrdinary.CompetitorCountMask
open RepairOrdinary.CloseoutRowsEstimatorCoefficients
open RepairOrdinary.CompetitorCrossScheduler (producer)
open RepairSource.CloseoutFinal P1Independent

attribute [local irreducible] Warm.machine Warm.input WarmFields.words
  CompetitorCrossScheduler.producer install dockH

def tapes (p : Program) := (Reuse.tapes p+7)+3
def scanSlots (p : Program) : Fin (Reuse.tapes p+3) → Fin (tapes p) :=
  Fin.addCases (fun j => (j.castAdd 7).castAdd 3)
    (fun j => j.natAdd (Reuse.tapes p+7))

theorem scan_injective (p : Program) : Function.Injective (scanSlots p) := by
  intro i j he
  have hv := congrArg Fin.val he
  revert hv
  refine Fin.addCases (m:=Reuse.tapes p) (n:=3) (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (m:=Reuse.tapes p) (n:=3) (fun b => ?_) (fun b => ?_) j
  · intro hv
    simp only [scanSlots,Fin.addCases_left,Fin.val_castAdd] at hv
    exact congrArg (Fin.castAdd 3) (Fin.ext hv)
  · intro hv
    simp only [scanSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    have := a.isLt
    omega
  · intro hv
    simp only [scanSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
    have := b.isLt
    omega
  · intro hv
    simp only [scanSlots,Fin.addCases_right,Fin.val_natAdd] at hv
    exact congrArg (Fin.natAdd (Reuse.tapes p)) (Fin.ext (by omega))

def bank {A : Type} (p : Program) (base : Fin (Reuse.tapes p) → A)
    (fields : Fin 7 → A) (scanner : Fin 3 → A) : Fin (tapes p) → A :=
  Fin.addCases (Fin.addCases base fields) scanner

theorem projected {A : Type} (p : Program) (base : Fin (Reuse.tapes p) → A)
    (fields : Fin 7 → A) (scanner : Fin 3 → A) (j : Fin (Reuse.tapes p+3)) :
    bank p base fields scanner (scanSlots p j) = Fin.addCases base scanner j := by
  refine Fin.addCases (m:=Reuse.tapes p) (n:=3) (fun _ => ?_) (fun _ => ?_) j <;>
    simp only [bank,scanSlots,Fin.addCases_left,Fin.addCases_right]

theorem installed (p : Program) (base next : Fin (Reuse.tapes p) → List Bool)
    (fields : Fin 7 → List Bool) (scanner nextScanner : Fin 3 → List Bool) :
    install (scanSlots p) (bank p base fields scanner) (Fin.addCases next nextScanner) =
      bank p next fields nextScanner := by
  funext i
  refine Fin.addCases (m:=Reuse.tapes p+7) (n:=3) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=Reuse.tapes p) (n:=7) (fun k => ?_) (fun k => ?_) j
    · have he : (k.castAdd 7).castAdd 3 = scanSlots p (k.castAdd 3) := by
        simp only [scanSlots,Fin.addCases_left]
      rw [he,install_slot _ (scan_injective p)]
      simp only [scanSlots,bank,Fin.addCases_left]
    · have avoid : ∀ z,scanSlots p z ≠ (k.natAdd (Reuse.tapes p)).castAdd 3 := by
        intro z
        refine Fin.addCases (m:=Reuse.tapes p) (n:=3) (fun l => ?_) (fun l => ?_) z
        all_goals
          intro he
          have hv := congrArg Fin.val he
          simp only [scanSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_natAdd,Fin.val_castAdd] at hv
          have := k.isLt
          have := l.isLt
          omega
      rw [install_other _ _ _ _ avoid]
      simp only [bank,Fin.addCases_left,Fin.addCases_right]
  · have he : j.natAdd (Reuse.tapes p+7) = scanSlots p (j.natAdd (Reuse.tapes p)) := by
      simp only [scanSlots,Fin.addCases_right]
    rw [he,install_slot _ (scan_injective p)]
    simp only [scanSlots,bank,Fin.addCases_right]

noncomputable def scanner (p : Program) :=
  RecoveryFocus.machine (scanSlots p)
    (RecoveryFocus.machine (C10RowScannerDock.slots p) C10RowScannerReload.machine)
noncomputable def machine (a : WilliamsAlgorithm) :=
  Composition.machine (scanner (producer a))
    (TapeEmbedding.machine 3 (WarmTransaction.machine a))

noncomputable def heads (p : Program) (out : List Bool) : Fin (tapes p) → Nat :=
  bank p (bankHeads p out) (fun _ => 0) (fun _ => 0)

noncomputable def input (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (old : Fin (WholePrefix.tapes p) → List Bool) (out : List Bool) : Fin (tapes p) → List Bool :=
  bank p (Function.update (exitTapes p D old out) (Reuse.native p)
    (ZeroPadding.pad C (Header.stream row)))
    (WarmFields.words row Q q den select) (C10RowScannerReload.fields row)

noncomputable def output (p : Program) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (out : List Bool) : Fin (tapes p) → List Bool :=
  Fin.addCases (WarmTransaction.output p row C D Q q den select out) (C10RowScannerReload.fields row)

noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (D Q : Nat) :=
  C10RowScannerReload.budget row D + 1 + (2*D+4+1+C10RowCommonCapacity.budget a row Q D)

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : Nat)
    (q : CompetitorValidity.Estimate) (den : Nat)
    (f : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Nat)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (old : Fin (WholePrefix.tapes (producer a)) → List Bool) (out : List Bool)
    (hcapacity : old (Retained.capacity (producer a)) = List.replicate C true)
    (hCD : C ≤ D) (hd : row.d ≤ D) (hp : row.p ≤ D) (hDpos : 1 ≤ D)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hf : ∀ i j, f i j < 2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : Int)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D) :
    let word := Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
      (selected (CompetitorSelectedCells.cells row.odd f select)).sum den
    Step (machine a) (budget a row D Q)
      (heads (producer a) out) (input (producer a) row C D Q q den select old out)
      (heads (producer a) (out++word)) (output (producer a) row C D Q q den select (out++word)) := by
  dsimp only
  let p := producer a
  have sh := ScannerBare.run p row C D old out hcapacity hCD hd hp hDpos
  have docked := sh.dock (scanSlots p) (scan_injective p) (heads p out)
    (input p row C D Q q den select old out)
    (projected p (bankHeads p out) (fun _ => 0) (fun _ => 0))
    (projected p _ (WarmFields.words row Q q den select) (C10RowScannerReload.fields row))
  have dh : dockH (scanSlots p) (heads p out) (C10RowScannerDock.heads p out) = heads p out :=
    dockH_existing _ _ _ (projected p (bankHeads p out) (fun _ => 0) (fun _ => 0))
  rw [dh] at docked
  change Step (scanner p) _ _ _ _
    (install (scanSlots p) (bank p _ _ _) (Fin.addCases _ _)) at docked
  rw [installed] at docked
  have wh := WarmTransaction.entry_heads a row C D Q q den select out
  unfold C10RowCommonCapacity.entry at wh
  rw [C10RowFrameJoin.entry_heads] at wh
  have warm := (WarmTransaction.run a row C D Q q den f select out hC hQ hf hc hD).embed
    (fun _ : Fin 3 => 0) (C10RowScannerReload.fields row)
  have ih : Fin.addCases (WarmPrepare.heads p out) (fun _ : Fin 3 => 0) = heads p out := by
    rw [← wh]
    rfl
  have it : Fin.addCases (WarmTransaction.input p row C D Q q den select out)
      (C10RowScannerReload.fields row) =
      bank p (ScannerBare.bareBank p row C D out) (WarmFields.words row Q q den select)
        (C10RowScannerReload.fields row) := by
    rw [WarmTransaction.input_eq]
    rfl
  exact docked.seq (warm.congr_in ih it)

theorem budget_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : Nat)
    (hC : (Header.stream row).length ≤ C) (hQ : Q ≤ (EquationRow.request row).p)
    (hD : Driver.value a row.d row.p row.cuts.length C ≤ D) : budget a row D Q ≤ 11*D+80 := by
  have hw := WarmTransaction.budget_le a row C D Q hC hQ hD
  have hf := (Driver.fuel_bound a row C Q hC hQ).trans hD
  have he := Warm.split_budget a row C Q
  unfold Scanned.budget at he
  unfold budget C10RowScannerReload.budget
  omega

end NearCubicWires.P1Closure.ScannedRow
