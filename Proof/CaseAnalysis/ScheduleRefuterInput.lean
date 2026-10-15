import Proof.CaseAnalysis.ScheduleRefuterPrefixBound

/-! The actual schedule/refuter input contains only the final address.
This literal equality lets the final ordinary program alias that one tape
onto its input port without a copy, initialized work, or another length scan. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
open LocalBitMultitape RepairOrdinary CloseoutRetainedRefuter
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem guarded_input (w : ℕ) (bits : List Bool) (i : Fin (Guarded.tapes w)) :
    Guarded.input w bits i=if i.val=w+6 then frame bits else [] := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Guarded.input,Fin.addCases_left,Fin.val_castAdd,Cold.input]
    rfl
  · simp only [Guarded.input,Fin.addCases_right,Fin.val_natAdd]
    have h: w+6 < Cold.tapes w := (Cold.extra w 0).isLt
    rw [if_neg (by omega)]

theorem address_value (w : ℕ) : (addressPort w).val=w+6 := rfl

theorem literal_input (w : ℕ) (r : OrdinaryOracleProgram) (bits : List Bool)
    (i : Fin (CloseoutRetainedRefuter.tapes (Guarded.tapes w) r)) :
    CloseoutRetainedRefuter.input r (Guarded.input w bits) i=
      if i.val=(old r (addressPort w)).val then frame bits else [] := by
  have ha: w+6 < Guarded.tapes w := (addressPort w).isLt
  by_cases h:i.val<Guarded.tapes w
  · simp only [CloseoutRetainedRefuter.input,dif_pos h,guarded_input]
    rfl
  · have he : i.val≠(old r (addressPort w)).val := by
      change i.val≠w+6
      omega
    simp only [CloseoutRetainedRefuter.input,dif_neg h,if_neg he]

end
end NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix
