import Proof.CaseAnalysis.RowsEstimatorMetadataBatch
import Proof.CaseAnalysis.RowsEstimatorActual

/-! The seven literal caller fields of the original Warm estimator bank.
No matrix, count packet, or source stream is supplied by these fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
open LocalBitMultitape MatrixScoreBatch RepairRepresentation CompetitorCountMask
open CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def promote (p : Program) (i : Fin (CompetitorCountTableRecord.tapes p)) : Fin (WholePrefix.tapes p) :=
  (i.natAdd 130).natAdd 70
def slots (p : Program) : Fin 7 → Fin (WholePrefix.tapes p) :=
  ![promote p (((CompetitorCountTable.fresh p 1).castAdd 92).castAdd 27),
    promote p (((CompetitorCountTable.fresh p 3).castAdd 92).castAdd 27),
    promote p ((CompetitorSelectedTable.fresh p 0).castAdd 27),
    promote p ((22 : Fin 27).natAdd (CompetitorSelectedTable.tapes p)),
    promote p ((23 : Fin 27).natAdd (CompetitorSelectedTable.tapes p)),
    promote p ((24 : Fin 27).natAdd (CompetitorSelectedTable.tapes p)),
    promote p ((25 : Fin 27).natAdd (CompetitorSelectedTable.tapes p))]
def words (row : EquationRow.Input) (Q : ℕ) (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) : Fin 7 → List Bool :=
  let b := scalarWidth (EquationRow.request row) Q
  ![List.replicate Q true,[row.odd],
    mask (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select),
    frame (SignedSortKey.binary (CompetitorRationalDecision.width b) q.positive),
    frame (SignedSortKey.binary (CompetitorRationalDecision.width b) q.negative),
    frame (SignedSortKey.binary (CompetitorRationalDecision.width b) q.denominator),
    frame (SignedSortKey.binary b denominator)]

theorem slots_val (p : Program) (i : Fin 7) :
    (slots p i).val=(![893,895,1016,1130,1131,1132,1133] : Fin 7 → ℕ) i+p.tapeCount := by
  fin_cases i <;> simp [slots,promote,CompetitorCountTable.fresh,CompetitorSelectedTable.fresh,
    CompetitorSelectedTable.tapes,CompetitorCountTable.tapes,CompetitorCountBanks.tapes,
    CompetitorCrossScheduler.tapes] <;> omega

theorem injective (p : Program) : Function.Injective (slots p) := by
  intro i j he
  have hv := congrArg (fun z : Fin (WholePrefix.tapes p) => z.val) he
  rw [slots_val,slots_val] at hv
  fin_cases i <;> fin_cases j <;> simp at hv ⊢

theorem at_promote (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool)
    (i : Fin (CompetitorCountTableRecord.tapes p)) (hi : i.val≠0) :
    Warm.input p row C Q q denominator select (promote p i)=
      Table.input p (EquationRow.request row) Q row.odd q denominator
        (CompetitorSelectedCells.cells row.odd (fun _ _=>0) select) i := by
  unfold Warm.input Warm.supplied promote
  erw [Fin.addCases_right]
  unfold WholePrefix.extra
  rw [if_neg (by simp)]
  unfold Record.input Consumer.input
  erw [Fin.addCases_right]
  simp only [Consumer.extra,hi,if_false]

theorem projected (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (i : Fin 7) :
    Warm.input p row C Q q denominator select (slots p i)=words row Q q denominator select i := by
  fin_cases i
  all_goals dsimp only [slots,Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals erw [at_promote p row C Q q denominator select _ (by
    simp [CompetitorCountTable.fresh,CompetitorSelectedTable.fresh,CompetitorCountBanks.tapes,
      CompetitorCrossScheduler.tapes,CompetitorCountTable.tapes,CompetitorSelectedTable.tapes])]
  all_goals simp! [Table.input,CompetitorSelectedTable.extend,CompetitorSelectedTable.extra,
    CompetitorCountTable.input,CompetitorCountTable.extend,CompetitorCountTable.metadata,
    CompetitorCountTable.fresh,CompetitorSelectedTable.fresh,CountRequest.extra,words]
  all_goals erw [Fin.addCases_left,Fin.addCases_left,Fin.addCases_right]
  all_goals rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmFields
