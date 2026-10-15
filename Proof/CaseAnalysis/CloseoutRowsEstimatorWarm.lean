import Proof.CaseAnalysis.RowsEstimatorScanned

/-! The original header/framer and row/Williams remainder start directly
from the paid scanner endpoint. This is the consumer after D allocation;
the exact scanner output replaces no source, count or table computation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Warm
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (p : Program) (i : Fin 59) : Fin (WholePrefix.tapes p):=
  (Framed.slots i).castAdd 2 |>.castAdd (CloseoutRowsRawRecord.tapes p)
theorem header_injective (p : Program) : Function.Injective (headerSlots p) := by
  intro i j he
  apply Framed.injective
  exact Fin.ext (congrArg (fun k : Fin (WholePrefix.tapes p)=>k.val) he)
noncomputable def first (p : Program):=RecoveryFocus.machine (headerSlots p) Header.framed
noncomputable def core {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s):=
  Composition.machine (first p) (WholePrefix.last p callee)
noncomputable def machine (a : WilliamsAlgorithm):=core (producer a) (Whole.callee a)
noncomputable def supplied (p : Program) (row : EquationRow.Input) (C : ℕ)
    (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool) :=
  Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (motive:=fun _=>List Bool)
    (Scanned.output row C) (WholePrefix.extra p data)
noncomputable def input (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  supplied p row C (Record.input p row Q q denominator select)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ):=
  Header.framedBudget row+1+CloseoutRowsRawRecord.budget a row Q

theorem header_input (p : Program) (row : EquationRow.Input) (C : ℕ) (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool) (i : Fin 59) :
    supplied p row C data (headerSlots p i)=Header.framedInput row i := by
  simp only [supplied,headerSlots,Fin.addCases_left]
  have hs : (Framed.slots i).val<64 ∨ (Framed.slots i).val=64 ∨
      (Framed.slots i).val=65 ∨ (Framed.slots i).val=66 ∨ (Framed.slots i).val=67 := by omega
  have he : Scanned.output row C ((Framed.slots i).castAdd 2)=
      Framed.extend (Prepare.output row) (Framed.slots i) := by
    rcases hs with hs|hs|hs|hs|hs
    · let j : Fin 64:=⟨(Framed.slots i).val,hs⟩
      have hj : Framed.slots i=j.castAdd 4:=Fin.ext rfl
      rw [hj]
      change Scanned.output row C (j.castAdd 6)=_
      simp only [Scanned.output,Framed.extend,Fin.addCases_left]
    · rw [show Framed.slots i=64 from Fin.ext hs];rfl
    · rw [show Framed.slots i=65 from Fin.ext hs];rfl
    · rw [show Framed.slots i=66 from Fin.ext hs];rfl
    · rw [show Framed.slots i=67 from Fin.ext hs];rfl
  exact he.trans (Framed.projected_input row i)

private theorem left_initial {t s u : ℕ} (p : Machine t s) (q : Machine t u)
    (A : Fin t→List Bool) : Composition.leftConfig u (initialConfiguration p A)=
      initialConfiguration (Composition.machine p q) A := rfl

theorem prefix_run {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s)
    (row : EquationRow.Input) (C : ℕ) (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool)
    (source : ∀ i,i.val=0→data i=frame (EquationRowRaw.source row))
    (fuel : ℕ) (child : ExecutionReceipt (CloseoutRowsRawRecord.tapes p) s)
    (ch : LocalBitMultitape.run callee fuel data=some child) : ∃ actual,
    LocalBitMultitape.run (core p callee) (Header.framedBudget row+1+fuel)
      (supplied p row C data)=some actual ∧
      (∀ i,actual.final.tapes (WholePrefix.slots p i)=child.final.tapes i) := by
  obtain ⟨header,hh,ht,hh0,_hs⟩:=Header.framed_run row
  obtain ⟨before,hb,_,_bs,bh,bt,bkeep⟩:=RecoveryFocus.dock (headerSlots p) (header_injective p)
    Header.framed (Header.framedBudget row) (fun _=>0) (supplied p row C data) _
    (by intro j;rfl) (header_input p row C data) header hh
  have allH : ∀ i,before.final.heads i=0 := by
    intro i
    by_cases hi : ∃ j,headerSlots p j=i
    · obtain ⟨j,rfl⟩:=hi
      exact (bh j).trans (hh0 j)
    · exact (bkeep i (by simpa only [not_exists] using hi)).1
  have dataT (i : Fin (CloseoutRowsRawRecord.tapes p)) :
      before.final.tapes (WholePrefix.slots p i)=data i := by
    by_cases hz : i.val=0
    · have he : WholePrefix.slots p i=headerSlots p 57 := by
        apply Fin.ext
        simp [WholePrefix.slots,hz,headerSlots,Framed.slots]
      rw [he]
      exact (bt 57).trans (ht.trans (source i hz).symm)
    · have outside : ∀ j,headerSlots p j≠WholePrefix.slots p i := by
        intro j he
        have hv:=congrArg Fin.val he
        simp only [headerSlots,WholePrefix.slots,hz,ite_false,Fin.val_castAdd,Fin.val_natAdd] at hv
        have hbound:=(Framed.slots j).isLt
        omega
      rw [(bkeep _ outside).2]
      simp only [WholePrefix.slots,hz,ite_false,supplied,Fin.addCases_right,WholePrefix.extra]
  obtain ⟨tail,th,_,_ts,_th,tt,_tk⟩:=RecoveryFocus.dock (WholePrefix.slots p) (WholePrefix.injective p)
    callee fuel before.final.heads before.final.tapes _
    (fun i=>allH _) dataT child ch
  have htail : runFrom (WholePrefix.last p callee) fuel
      (Composition.restart before.final (WholePrefix.last p callee).start)=some tail:=th
  have hb' : LocalBitMultitape.run (first p) (Header.framedBudget row)
      (supplied p row C data)=some before:=hb
  have hj:=Composition.run_join (first p) (WholePrefix.last p callee) _ _ _ before tail hb' htail
  rw [left_initial] at hj
  exact ⟨Composition.joinedReceipt before tail,hj,tt⟩

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (hQ : Q≤(EquationRow.request row).p) (hf : ∀ i j,f i j<2^Q)
    (hc : ∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) : ∃ actual,
    LocalBitMultitape.run (machine a) (budget a row Q) (input (producer a) row C Q q denominator select)=some actual ∧
      actual.final.tapes (Whole.recordSlot (producer a))=
        Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      actual.final.tapes (Whole.matrixSlot (producer a))=physicalInput (EquationRow.request row) := by
  obtain ⟨child,ch,_cs,ct,_co,c0⟩:=Record.run a row Q f select q denominator hQ hf hc
  obtain ⟨actual,ha,ht⟩:=prefix_run (producer a) (Whole.callee a) row C
    (Record.input (producer a) row Q q denominator select)
    (Whole.source (producer a) row Q q denominator select) _ child ch
  exact ⟨actual,ha,(ht _).trans ct,(ht _).trans c0⟩

theorem split_budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ) :
    Scanned.budget row C+1+budget a row Q=Whole.budget a row C Q := by
  unfold Scanned.budget budget Whole.budget Cold.budget Framed.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Warm
