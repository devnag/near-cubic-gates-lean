import Proof.MachineModel.TopDownPaidRetiredPayload
import Proof.CaseAnalysis.RowsRawLoad

/-! The paid scanner/driver/count/retirement chain from literal cold words.
The native header and metadata are inputs; neither D nor a computed table is.
This is the row worker to be loaded from the physical sequential source. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReloadCore
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open CompetitorCrossScheduler (producer)
open P1TopDownPaidPayload (estimate port tapes)
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine
  Paid.driver Paid.warm Paid.retire Paid.retiredMachine RawRowJoin.machine

noncomputable def bank (a : WilliamsAlgorithm) (A : Fin 64→List Bool)
    (C : Nat) (fields : Fin 7→List Bool) : Fin (tapes a)→List Bool :=
  Fin.addCases
    (WarmPrepare.data (producer a)
      (Fin.addCases (Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) A (Scanned.extra C))
        (fun _ : Fin (CloseoutRowsRawRecord.tapes (producer a))=>[])) 0 0 fields)
    (fun _ : Fin (ScannedClean.tapes a)=>[])
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  bank a (Prepare.input row) C (WarmFields.words row Q estimate 1 select)
noncomputable def scanSlots (a : WilliamsAlgorithm) (i : Fin 64) : Fin (tapes a) :=
  Paid.old a (producer a) (WarmPrepare.old (producer a)
    ((i.castAdd 6).castAdd (CloseoutRowsRawRecord.tapes (producer a))))
noncomputable def scanner (a : WilliamsAlgorithm) := RecoveryFocus.machine (scanSlots a) Prepare.machine
noncomputable def machine (a : WilliamsAlgorithm) := Composition.machine (scanner a) (Paid.retiredMachine a)
noncomputable def fuel (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat) :=
  Prepare.budget row+1+P1TopDownPaidRetiredPayload.fuel a row C Q
noncomputable def rawMachine (a : WilliamsAlgorithm) := RawRowJoin.machine (machine a) (port a)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B : Nat) :=
  RawRowJoin.budget (fuel a row C Q) (scalarWidth (EquationRow.request row) Q) B

theorem scan_injective (a : WilliamsAlgorithm) : Function.Injective (scanSlots a) := by
  intro i j h
  exact Fin.ext (congrArg (fun z : Fin (tapes a)=>z.val) h)

theorem bank_scan (a : WilliamsAlgorithm) (A : Fin 64→List Bool) (C : Nat)
    (fields : Fin 7→List Bool) (i : Fin 64) : bank a A C fields (scanSlots a i)=A i := by
  simp only [bank,scanSlots,Paid.old,Fin.addCases_left,WarmPrepare.at_old]

set_option maxHeartbeats 1000000 in
theorem bank_installed (a : WilliamsAlgorithm) (A Z : Fin 64→List Bool) (C : Nat)
    (fields : Fin 7→List Bool) :
    install (scanSlots a) (bank a A C fields) Z=bank a Z C fields := by
  funext i
  by_cases h : i.val<64
  · let j : Fin 64:=⟨i.val,h⟩
    have he : i=scanSlots a j:=Fin.ext rfl
    rw [he,install_slot _ (scan_injective a),bank_scan]
  · have avoid : ∀ j,scanSlots a j≠i := by
      intro j he
      have hv:=congrArg (fun z : Fin (tapes a)=>z.val) he
      have hj:=j.isLt
      change j.val=i.val at hv
      omega
    rw [install_other _ _ _ _ avoid]
    revert h
    refine Fin.addCases (m:=WarmPrepare.tapes (producer a)) (n:=ScannedClean.tapes a)
      (fun j=>?_) (fun j _=>by simp only [bank,Fin.addCases_right]) i
    simp only [bank,Fin.addCases_left,WarmPrepare.data]
    refine Fin.addCases (m:=Reuse.tapes (producer a)) (n:=7)
      (fun k=>?_) (fun k _=>by simp only [Fin.addCases_right]) j
    simp only [Fin.addCases_left,WarmPrepare.bank]
    refine Fin.addCases (m:=WholePrefix.tapes (producer a)+1) (n:=2)
      (fun k=>?_) (fun k _=>by simp only [Fin.addCases_right]) k
    simp only [Fin.addCases_left]
    refine Fin.addCases (m:=WholePrefix.tapes (producer a)) (n:=1)
      (fun k=>?_) (fun k _=>by simp only [Fin.addCases_right]) k
    simp only [Fin.addCases_left]
    refine Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes (producer a))
      (fun k=>?_) (fun k _=>by simp only [Fin.addCases_right]) k
    simp only [Fin.addCases_left]
    refine Fin.addCases (m:=64) (n:=6) (fun k hk=>?_) (fun k _=>by simp only [Fin.addCases_right]) k
    have hb:=k.isLt
    simp only [Fin.val_castAdd] at hk
    omega

theorem scanned_bank (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :
    bank a (Prepare.output row) C (WarmFields.words row Q estimate 1 select)=
      P1TopDownPaidPayload.input a row C Q select := by
  unfold P1TopDownPaidPayload.input Paid.input Paid.publicInput
  have bare : WarmFields.bare (producer a) row C=
      Fin.addCases (Fin.addCases (m:=64) (n:=6) (motive:=fun _=>List Bool) (Prepare.output row) (Scanned.extra C))
        (fun _ : Fin (CloseoutRowsRawRecord.tapes (producer a))=>[]) := by
    funext i
    simp only [WarmFields.bare,Warm.supplied,Scanned.output]
    refine Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes (producer a))
      (fun _=>by simp only [Fin.addCases_left]) (fun j=>?_) i
    simp [WholePrefix.extra]
  rw [bare]
  unfold WarmPrepare.live
  have hu (A : Fin (WholePrefix.tapes (producer a))→List Bool) (fields : Fin 7→List Bool) :
      Function.update (WarmPrepare.data (producer a) A 0 0 fields) (WarmPrepare.spare (producer a)) []=
        WarmPrepare.data (producer a) A 0 0 fields := by
    conv_lhs => arg 3; rw [←WarmPrepare.at_spare (producer a) A 0 0 fields]
    exact Function.update_eq_self _ _
  rw [hu]
  rfl

theorem scan_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :
    Step (scanner a) (Prepare.budget row) (fun _=>0) (input a row C Q select)
      (fun _=>0) (P1TopDownPaidPayload.input a row C Q select) := by
  obtain ⟨r,hr,ht,hh,hs⟩:=Prepare.ready row
  have base : Step Prepare.machine (Prepare.budget row) (fun _=>0) (Prepare.input row)
      (fun _=>0) (Prepare.output row):=⟨r,hr,funext hh,ht,hs⟩
  have h:= base.dock (scanSlots a) (scan_injective a)
    (fun _=>0) (input a row C Q select) (by intro i;rfl) (bank_scan a _ _ _)
  exact h.congr (dockH_existing _ _ _ (by intro i;rfl))
    ((bank_installed a _ _ _ _).trans (scanned_bank a row C Q select))

private theorem start_step {t sp sq su n : Nat}
    (first : Machine t sp) (second : Machine t sq) (last : Machine t su)
    (hin hout : Fin t→Nat) (tin tout : Fin t→List Bool)
    (r : ExecutionReceipt t (sp+sq+su))
    (hr : runFrom (Composition.machine (Composition.machine first second) last) n
      (Composition.leftConfig su (WarmPrepared.startWith first second hin tin))=some r)
    (hh : r.final.heads=hout) (ht : r.final.tapes=tout) :
    Step (Composition.machine (Composition.machine first second) last) n hin tin hout tout := by
  rw [Paid.nested_start first second last hin tin] at hr
  exact Step.of_run hr hh ht

set_option maxHeartbeats 1000000 in
theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q B R : Nat)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (out : List Bool)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p)
    (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : Int)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat))
    (hR : fuel a row C Q≤R)
    (hB : RowPayload.budget (scalarWidth (EquationRow.request row) Q)≤B)
    (hBR : B+1≤R) :
    let b := scalarWidth (EquationRow.request row) Q
    let count := (selected (CompetitorSelectedCells.cells row.odd f select)).sum
    ∃ Z : Fin (tapes a)→List Bool,
      Step (rawMachine a) (budget a row C Q B)
        (RawRowJoin.heads (tapes a) out)
        (RawRowJoin.bank (RawRowJoin.padded (port a) B (input a row C Q select)) R B out)
        (RawRowJoin.heads (tapes a) (out++SignedSortKey.binary b count))
        (RawRowJoin.bank (RawRowJoin.padded (port a) B (Function.update Z (port a) [])) R B
          (out++SignedSortKey.binary b count)) := by
  dsimp only
  let p:=producer a
  have hw:=Paid.warm_owned_run a row C Q estimate 1 f select [] hC hQ hf hc
  simp only [List.nil_append] at hw
  have ho:=Paid.retire_owned_join a p row C (Driver.value a row.d row.p row.cuts.length C)
    _ _ _ (WarmFields.words row Q estimate 1 select) (Paid.warmMachine a)
    (Paid.warmEntry a row C Q estimate 1 select []) hw
  obtain ⟨r,hr,hh,_hs,clean⟩:=ho.clean
  unfold Paid.warmMachine Paid.warmEntry at hr
  have printed:=start_step (Paid.driver a) (Paid.warm a) (Paid.retire a p)
    (Paid.heads a p []) _ (P1TopDownPaidPayload.input a row C Q select) _ r hr hh rfl
  have printed' : Step (Paid.retiredMachine a) (P1TopDownPaidRetiredPayload.fuel a row C Q)
      (fun _=>0) (P1TopDownPaidPayload.input a row C Q select)
      (Paid.heads a p (Stream.recordWord (scalarWidth (EquationRow.request row) Q) estimate
        (selected (CompetitorSelectedCells.cells row.odd f select)).sum 1)) r.final.tapes := by
    unfold Paid.retiredMachine Paid.warmMachine
    exact printed.congr_in (P1TopDownPaidPayload.empty_heads a) rfl
  have joined:= (scan_run a row C Q select).seq printed'
  exact ⟨r.final.tapes,RawRowState.run (machine a) (port a) (fuel a row C Q)
    (scalarWidth (EquationRow.request row) Q) B R estimate
    (selected (CompetitorSelectedCells.cells row.odd f select)).sum 1 _ _ _ out
    joined clean.output hR hB hBR⟩

end NearCubicWires.P1TopDownPaidReloadCore
