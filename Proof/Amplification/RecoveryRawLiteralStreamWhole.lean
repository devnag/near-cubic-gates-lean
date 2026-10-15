import Proof.Amplification.RecoveryRawLiteralStreamCalls

/-! Actual raw-literal decoding followed, only for a present cell, by the
paid skip of its unused witness fields. No equality to those fields is used. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem stream_run (x : State) (hx : x.data.data.Valid) :
    ∃ r,runFrom machine (cost x) (x.cfg machine.start)=some r ∧
      r.final=(output x).cfg r.final.control ∧ r.steps ≤ cost x := by
  obtain ⟨first,hr0,hf0,_⟩ := literal_run x hx
  have hh0 : first.final.heads 28=0 := by rw [hf0]; rfl
  have ht0 : first.final.tapes 28=[(decoded x).data.present] := by rw [hf0]; rfl
  cases ha : (decoded x).data.present
  · rw [ha] at ht0
    have hrun := RecoveryGatedSequence.reject_run literalMachine skipMachine 28 (RecoveryRawLiteral.cost x.data) _ first hr0 hh0 ht0
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have hl : RecoveryRawLiteral.cost x.data+1 ≤ cost x := by unfold cost; omega
    have hm := runFrom_moreFuel machine (RecoveryRawLiteral.cost x.data+1)
      (cost x-(RecoveryRawLiteral.cost x.data+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    have ho : output x=decoded x := by simp only [output,ha,Bool.false_eq_true,ite_false]
    refine ⟨r,hm,?_,hb.trans hl⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf0,ho]; rfl
    · rw [hf,hf0,ho]; rfl
  · obtain ⟨last,hr1,hf1,_⟩ := skip_run x
    have he : RecoveryCalls.restarted skipMachine first.final.heads first.final.tapes=(decoded x).cfg skipMachine.start := by
      rw [hf0]; rfl
    rw [←he] at hr1
    rw [ha] at ht0
    have hrun := RecoveryGatedSequence.accept_run literalMachine skipMachine 28 (RecoveryRawLiteral.cost x.data)
      (3*(2*x.width)+2) _ first last hr0 hh0 ht0 hr1
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have ho : output x=skipped x := by simp only [output,ha,ite_true]
    refine ⟨r,hr,?_,hb⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf1,ho]; rfl
    · rw [hf,hf1,ho]; rfl

theorem output_data (x : State) : (output x).data=RecoveryRawLiteral.output x.data := by
  unfold output
  split <;> rfl

theorem output_source (x : State) : (output x).source=x.source := by
  unfold output
  split <;> rfl

theorem output_pos (x : State) :
    (output x).pos=if RadixSemantics.value x.data.data.bits=0 then x.pos else x.pos+4*x.width := by
  have hp : (decoded x).data.present=decide (RadixSemantics.value x.data.data.bits≠0) := RecoveryRawLiteral.output_present x.data
  unfold output
  rw [hp]
  by_cases hz : RadixSemantics.value x.data.data.bits=0 <;> simp only [hz,ne_eq,not_true_eq_false,decide_false,
    Bool.false_eq_true,ite_false,not_false_eq_true,decide_true,ite_true] <;> rfl

theorem cost_bound (x : State) : cost x ≤ 1048576*(x.width+1)^2 := by
  have h := RecoveryRawLiteral.cost_bound x.data
  change RecoveryRawLiteral.cost x.data ≤ 524288*(x.width+1)^2 at h
  unfold cost
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralStream
