import Proof.CaseAnalysis.RowsEstimatorWholePrefix
import Proof.CaseAnalysis.RowsEstimatorRecord

/-! One shared physical estimator from actual native cut bytes at their
append cursor. The original row/Williams full table runs before the selected
SUM. The live metadata producers remain explicit in the input bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Whole
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def callee (a : WilliamsAlgorithm):=
  CloseoutRowsRawRecord.machine (producer a) (CompetitorCountTableRecord.machine a)
noncomputable def machine (a : WilliamsAlgorithm):=WholePrefix.machine (producer a) (callee a)
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool):=
  WholePrefix.entry (producer a) (callee a) row C (Record.input (producer a) row Q q denominator select)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Cold.budget row C+1+CloseoutRowsRawRecord.budget a row Q
noncomputable def envelope (a : WilliamsAlgorithm) (row : EquationRow.Input) (C : ℕ):=
  10000*(Cold.scale row C)^2+1+CloseoutRowsRawRecord.envelope a row
def recordSlot (p : Program):=WholePrefix.slots p (CloseoutRowsRawRecord.receive p (CompetitorCountTableRecord.slots p 117))
def matrixSlot (p : Program):=WholePrefix.slots p (CloseoutRowsRawRecord.receive p (CompetitorCountTableRecord.slots p 0))

theorem source (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (i : Fin (CloseoutRowsRawRecord.tapes p)) (hi:i.val=0) :
    Record.input p row Q q denominator select i=frame (EquationRowRaw.source row):=by
  have he:i=(0 : Fin 130).castAdd (CompetitorCountTableRecord.tapes p):=Fin.ext hi
  rw [he]
  rfl

theorem run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (f : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (hC:(Header.stream row).length≤C) (hQ:Q≤(EquationRow.request row).p)
    (hf:∀ i j,f i j<2^Q)
    (hc:∀ i : Fin ((EquationRow.request row).U*(EquationRow.request row).U),
      Int.ModEq ((2 : ℤ)^Q)
        (SupplierPrinter.weightedDominance (leftScore (EquationRow.request row))
          (rightScore (EquationRow.request row)) (weight (EquationRow.request row)) i.divNat i.modNat)
        (f i.divNat i.modNat)) :
    ∃ actual,runFrom (machine a) (budget a row C Q) (entry a row C Q q denominator select)=some actual ∧
      actual.steps≤envelope a row C ∧
      actual.final.tapes (recordSlot (producer a))=
        Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator ∧
      actual.final.heads (recordSlot (producer a))=
        (Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
          (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator).length ∧
      actual.final.tapes (matrixSlot (producer a))=physicalInput (EquationRow.request row):=by
  obtain ⟨child,ch,cs,ct,co,c0⟩:=Record.run a row Q f select q denominator hQ hf hc
  obtain ⟨actual,ha,hs,hh,ht⟩:=WholePrefix.prefix_run (producer a) (callee a) row C hC
    (Record.input (producer a) row Q q denominator select)
    (source (producer a) row Q q denominator select) _ child ch
  have hb:=Cold.budget_bound row C
  refine ⟨actual,ha,?_,(ht _).trans ct,(hh _).trans co,(ht _).trans c0⟩
  unfold envelope
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Whole
