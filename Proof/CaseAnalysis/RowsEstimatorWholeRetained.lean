import Proof.CaseAnalysis.RowsEstimatorWhole
import Proof.CaseAnalysis.RowsEstimatorWholePrefixRetained

/-! The original complete estimator also returns its external native source
head and native capacity, needed by the enclosing fixed-row loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholeRetained
open LocalBitMultitape MatrixScoreBatch RepairRepresentation Whole
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

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
      actual.final.tapes (matrixSlot (producer a))=physicalInput (EquationRow.request row) ∧
      actual.final.heads ((52 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes (producer a)))=0 ∧
      actual.final.tapes ((68 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes (producer a)))=List.replicate C true:=by
  obtain ⟨child,ch,cs,ct,co,c0⟩:=Record.run a row Q f select q denominator hQ hf hc
  obtain ⟨actual,ha,hs,hh,ht,houtside,hCword⟩:=WholePrefixRetained.run (producer a) (callee a) row C hC
    (Record.input (producer a) row Q q denominator select)
    (source (producer a) row Q q denominator select) _ child ch
  have hb:=Cold.budget_bound row C
  refine ⟨actual,ha,?_,(ht _).trans ct,(hh _).trans co,(ht _).trans c0,houtside 52 (by decide),hCword⟩
  unfold envelope
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WholeRetained
