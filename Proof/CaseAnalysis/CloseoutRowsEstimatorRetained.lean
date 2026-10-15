import Proof.CaseAnalysis.RowsEstimatorAppendReturn
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The actual cold estimator retains its original native-bank capacity.
This is the same physical word subsequently used by the scratch sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Retained
open LocalBitMultitape RepairRepresentation RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (p : Program) : Fin (WholePrefix.tapes p):=(68 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p)

theorem cold_capacity : NoWrite Cold.machine 68:=by
  apply composition
  · change NoWrite (RecoveryFocus.machine Cold.slots CompetitorRecordRewind.machine) (Cold.slots 1)
    apply focus _ (by decide)
    intro q bits a ha
    simp only [CompetitorRecordRewind.machine] at ha
    split_ifs at ha <;> cases ha <;>rfl
  · intro q bits a ha
    obtain ⟨b,_hb,he⟩:=Option.map_eq_some_iff.mp ha
    subst a
    change (TapeEmbedding.action 2 b).write ((0 : Fin 2).natAdd 68)=none
    simp only [TapeEmbedding.action,Fin.addCases_right]

theorem whole_capacity (a : WilliamsAlgorithm) : NoWrite (Whole.machine a) (capacity (CompetitorCrossScheduler.producer a)):=by
  apply composition
  · exact embedded _ Cold.machine 68 cold_capacity
  · apply unselected
    intro j he
    have hv:=congrArg Fin.val he
    simp only [WholePrefix.slots,capacity,Fin.val_castAdd] at hv
    split_ifs at hv <;>simp only [Fin.val_natAdd] at hv <;>omega

theorem capacity_input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :
    (Whole.entry a row C Q q denominator select).tapes (capacity (CompetitorCrossScheduler.producer a))=
      List.replicate C true:=by
  change WholePrefix.input (CompetitorCrossScheduler.producer a) row C
    (Record.input (CompetitorCrossScheduler.producer a) row Q q denominator select)
    ((68 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes (CompetitorCrossScheduler.producer a))) = _
  simp only [WholePrefix.input,Fin.addCases_left]
  change Cold.input row C ((0 : Fin 2).natAdd 68)=_
  simp only [Cold.input,Fin.addCases_right]
  rfl

theorem capacity_run (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (fuel : ℕ) (r : ExecutionReceipt _ _)
    (hr:runFrom (Whole.machine a) fuel (Whole.entry a row C Q q denominator select)=some r) :
    r.final.tapes (capacity (CompetitorCrossScheduler.producer a))=List.replicate C true:=
  (run_tape _ _ (whole_capacity a) _ _ _ hr).trans (capacity_input a row C Q q denominator select)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Retained
