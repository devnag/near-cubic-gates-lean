import Proof.Amplification.RecoveryRawSATCopyTapes

/-! Paid outer extraction and framed clause-code copy on the raw-SAT
workspace. Both calls return all local heads to zero for evaluator reuse. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem outer_ready (x : State) (hx : x.outer.Valid) :
    ReadyRun outerMachine (RecoveryStoredListCell.time x.outer.bits) x.tapes (outerStep x).tapes := by
  obtain ⟨base,hr,ht,hh,hs⟩ := RecoveryClauseState.cell_ready x.outer 0 hx
  have hrun := RecoveryBankPair.right_run (RecoveryClauseState.machine 0) (RecoveryStoredListCell.time x.outer.bits)
    (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes) base hr
    (fun _ : Fin 42=>0) (RecoveryClauseEvaluation.tapes x.clause x.valuation)
  obtain ⟨r,h,hsteps,hfinal⟩ := hrun
  have hi : RecoveryBankPair.cfg (fun _ : Fin 42=>0) (RecoveryClauseEvaluation.tapes x.clause x.valuation)
      (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes).heads
      (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes).tapes
      (initialConfiguration (RecoveryClauseState.machine 0) x.outer.tapes).control=initialConfiguration outerMachine x.tapes := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=42) (n:=28) (fun _=>?_) (fun _=>?_) i <;>
        simp [RecoveryBankPair.cfg,initialConfiguration]
    · rfl
  rw [hi] at h
  refine ⟨r,h,?_,?_,hsteps.trans hs⟩
  · rw [hfinal]
    change Fin.addCases (m:=42) (n:=28) (motive:=fun _=>List Bool)
      (RecoveryClauseEvaluation.tapes x.clause x.valuation) base.final.tapes=_
    rw [ht]
    rfl
  · intro i
    rw [hfinal]
    change Fin.addCases (m:=42) (n:=28) (motive:=fun _=>Nat) (fun _=>0) base.final.heads i=0
    refine Fin.addCases (m:=42) (n:=28) (fun _=>?_) (fun j=>?_) i
    · simp only [Fin.addCases_left]
    · simpa only [Fin.addCases_right] using hh j

theorem copy_ready (x : State) (bits : List Bool) (hw : bits.length=x.width)
    (hf : x.outer.fields 0=frame bits) :
    ReadyRun copyMachine (8*bits.length+8) x.tapes (copied x bits).tapes := by
  have hb : (frame x.clause.bits).length ≤ 2*bits.length+1 := by
    rw [frame_length,hw]
    exact Nat.le_refl _
  have h := (RecoveryRootRound.copy_ready bits (frame x.clause.bits) x.outer.capacity x.clause.capacity hb).focus
    copySlots copySlots_injective x.tapes (by
      intro j; fin_cases j
      · exact hf
      · rfl
      · rfl
      · rfl)
  have hi := copy_install x.tapes bits (max x.outer.capacity (2*bits.length+1))
    (max x.clause.capacity (4*bits.length+3)) hf
  rw [hi,←copied_tapes x bits hw] at h
  exact h

end NearCubicWires.RepairOrdinary.RecoveryRawSAT
