import Proof.Amplification.RecoveryMarkerClauseCalls

/-! One whole marker clause load executes the outer presence test and,
only when present, copies its actual head code into the literal bank. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loadMachine := RecoveryGatedSequence.machine outerMachine copyMachine 52
def loadCost (x : State) := RecoveryStoredListCell.time x.outer.bits+(8*(headWord x).length+8)+2
def loaded (x : State) := if value x.outer.bits=0 then outerStep x else copied (outerStep x) (headWord x)

theorem head_width (x : State) (hx : x.Valid) : (headWord x).length=x.width :=
  (RecoveryCellStore.headWord_length x.outer.bits).trans hx.2.2
theorem head_field (x : State) (hz : value x.outer.bits≠0) :
    (outerStep x).outer.fields 0=frame (headWord x) := by
  change (x.outer.after 0).fields 0=_
  simp only [RecoveryClauseState.State.after,hz,ite_false,Function.update_self]
  rfl
theorem loaded_valid (x : State) (hx : x.Valid) : (loaded x).Valid := by
  unfold loaded
  split
  · exact outer_valid x hx
  · exact copied_valid _ _ (outer_valid x hx) (head_width x hx)
theorem loaded_width (x : State) (hx : x.Valid) : (loaded x).width=x.width := by
  unfold loaded
  split
  · rfl
  · exact head_width x hx

theorem load_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom loadMachine (loadCost x) (x.cfg loadMachine.start)=some r ∧
      r.final=(loaded x).cfg r.final.control ∧ r.steps ≤ loadCost x := by
  obtain ⟨first,hr0,ht0,hh0,_⟩ := outer_ready x hx.2.1
  have hf0 : first.final=(outerStep x).cfg first.final.control := by
    apply configuration_ext
    · rfl
    · exact funext hh0
    · exact ht0
  have hflag : first.final.tapes 52=[decide (value x.outer.bits≠0)] := by
    rw [hf0]
    change [(x.outer.after 0).flag]=_
    rw [RecoveryThreeCellReader.after_flag]
  by_cases hz : value x.outer.bits=0
  · have ht : first.final.tapes 52=[false] := by simpa only [hz,ne_eq,not_true_eq_false,decide_false] using hflag
    have hrun := RecoveryGatedSequence.reject_run outerMachine copyMachine 52
      (RecoveryStoredListCell.time x.outer.bits) _ first hr0 (hh0 52) ht
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have hbound : RecoveryStoredListCell.time x.outer.bits+1 ≤ loadCost x := by unfold loadCost; omega
    have hm := runFrom_moreFuel loadMachine _ (loadCost x-(RecoveryStoredListCell.time x.outer.bits+1)) _ r hr
    rw [Nat.add_sub_of_le hbound] at hm
    refine ⟨r,hm,?_,hb.trans hbound⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf0]; simp only [loaded,hz,ite_true]; rfl
    · rw [hf,hf0]; simp only [loaded,hz,ite_true]; rfl
  · obtain ⟨last,hr1,ht1,hh1,_⟩ := copy_ready (outerStep x) (headWord x) (head_width x hx) (head_field x hz)
    have hi : RecoveryCalls.restarted copyMachine first.final.heads first.final.tapes=
        initialConfiguration copyMachine (outerStep x).tapes := by
      apply configuration_ext
      · rfl
      · exact funext hh0
      · exact ht0
    unfold run at hr1
    rw [←hi] at hr1
    have ht : first.final.tapes 52=[true] := by simpa only [decide_eq_true hz] using hflag
    have hrun := RecoveryGatedSequence.accept_run outerMachine copyMachine 52
      (RecoveryStoredListCell.time x.outer.bits) (8*(headWord x).length+8) _ first last hr0 (hh0 52) ht hr1
    obtain ⟨r,hr,hb,hf⟩ := hrun
    refine ⟨r,hr,?_,hb⟩
    apply configuration_ext
    · rfl
    · rw [hf]
      exact funext hh1
    · rw [hf,ht1]
      simp only [loaded,hz,ite_false]
      rfl

theorem load_cost_bound (x : State) (hx : x.Valid) : loadCost x ≤ 524288*(x.width+1)^2 := by
  have hc := RecoveryStoredListCell.time_bound x.outer.bits
  unfold RecoveryStoredListCell.budget at hc
  rw [hx.2.2] at hc
  unfold loadCost
  rw [head_width x hx]
  nlinarith only [hc,show 0<(x.width+1)^2 by positivity]

end NearCubicWires.RepairOrdinary.RecoveryMarkerClause
