import Proof.Amplification.RecoveryRawLiteralCalls

/-! One actual raw literal: the cell-presence gate precedes decoding.
Missing cells and invalid natural tags remain distinct physical outputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteral
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem literal_run (x : State) (hx : x.data.Valid) :
    ∃ r,runFrom machine (cost x) (x.cfg machine.start)=some r ∧
      r.final=(output x).cfg r.final.control ∧ r.steps ≤ cost x ∧ (output x).data.Valid := by
  obtain ⟨first,hr0,hf0,_⟩ := first_run x hx
  have hh0 : first.final.heads 28=0 := by rw [hf0]; rfl
  have ht0 : first.final.tapes 28=[(marked x).present] := by rw [hf0]; rfl
  cases ha : (marked x).present
  · rw [ha] at ht0
    have hrun := RecoveryGatedSequence.reject_run firstMachine decodeMachine 28 (firstCost x) _ first hr0 hh0 ht0
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have hl : firstCost x+1 ≤ cost x := by unfold cost; omega
    have hm := runFrom_moreFuel machine (firstCost x+1) (cost x-(firstCost x+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    have ho : output x=marked x := by simp only [output,ha,Bool.false_eq_true,ite_false]
    refine ⟨r,hm,?_,hb.trans hl,output_valid x hx⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf0,ho]; rfl
    · rw [hf,hf0,ho]; rfl
  · obtain ⟨last,hr1,hf1,_⟩ := decode_run x hx ha
    have he : RecoveryCalls.restarted decodeMachine first.final.heads first.final.tapes=(marked x).cfg decodeMachine.start := by
      rw [hf0]; rfl
    rw [←he] at hr1
    rw [ha] at ht0
    have hrun := RecoveryGatedSequence.accept_run firstMachine decodeMachine 28 (firstCost x)
      (RecoveryCheckedLiteral.time (literal x)) _ first last hr0 hh0 ht0 hr1
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have ho : output x=decoded x := by simp only [output,ha,ite_true]
    refine ⟨r,hr,?_,hb,output_valid x hx⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf1,ho]; rfl
    · rw [hf,hf1,ho]; rfl

theorem output_present (x : State) :
    (output x).present=decide (RadixSemantics.value x.data.bits≠0) := by
  have h : (output x).present=(marked x).present := by
    unfold output
    split <;> rfl
  exact h.trans (marked_present x)

theorem output_tag (x : State) (hx : RadixSemantics.value x.data.bits≠0) :
    (output x).data.result=decide ((Nat.unpair (Nat.unpair (RadixSemantics.value x.data.bits-1)).1).1 ≤ 1) := by
  have hp : (marked x).present=true := by rw [marked_present]; exact decide_eq_true hx
  rw [output,if_pos hp]
  change (RecoveryCheckedLiteral.checkedState (stepped x).data 0 (literal x)).result=_
  rw [RecoveryClauseEvaluation.checked_tag]
  rw [show RadixSemantics.value (literal x)=(Nat.unpair (RadixSemantics.value x.data.bits-1)).1 from
    RecoveryCellStore.head_value x.data.bits hx]

theorem output_bits (x : State) : (output x).data.bits=(stepped x).data.bits := by
  unfold output
  split <;> rfl

theorem output_width (x : State) : (output x).data.bits.length=x.data.bits.length := by
  rw [output_bits]
  exact RecoveryClauseState.after_length x.data 0

theorem output_tail (x : State) (hx : RadixSemantics.value x.data.bits≠0) :
    RadixSemantics.value (output x).data.bits=(Nat.unpair (RadixSemantics.value x.data.bits-1)).2 := by
  rw [output_bits]
  change RadixSemantics.value (x.data.after 0).bits=_
  rw [RecoveryClauseState.State.after,if_neg hx]
  exact RecoveryRawListStep.list_component false x.data.bits hx

theorem output_variable (x : State) (hx : RadixSemantics.value x.data.bits≠0) :
    (output x).data.fields 0=frame (RecoveryChildSelection.word false (literal x)) ∧
      RadixSemantics.value (RecoveryChildSelection.word false (literal x))=
        (Nat.unpair (Nat.unpair (RadixSemantics.value x.data.bits-1)).1).2 := by
  have hp : (marked x).present=true := by rw [marked_present]; exact decide_eq_true hx
  constructor
  · rw [output,if_pos hp]
    exact RecoveryClauseEvaluation.checked_variable (stepped x).data 0 (literal x)
  · rw [RecoveryClauseEvaluation.variable_value]
    rw [show RadixSemantics.value (literal x)=(Nat.unpair (RadixSemantics.value x.data.bits-1)).1 from
      RecoveryCellStore.head_value x.data.bits hx]

end NearCubicWires.RepairOrdinary.RecoveryRawLiteral
