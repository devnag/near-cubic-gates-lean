import Proof.Amplification.RecoveryRawLiteralBoundCalls

/-! Whole raw-literal inspector body: decode the actual list cell, advance
past unused certificate scalars, compare its index, and accumulate flags. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem body_run (x : State) (hx : x.Valid) :
    ∃ r,runFrom machine (cost x) (x.cfg machine.start)=some r ∧
      r.final=(output x).cfg r.final.control ∧ r.steps ≤ cost x := by
  obtain ⟨first,hr0,hf0,_⟩ := stream_run x hx
  have hh0 : first.final.heads 28=0 := by rw [hf0]; rfl
  have ht0 : first.final.tapes 28=[(decoded x).stream.data.present] := by rw [hf0]; rfl
  cases ha : (decoded x).stream.data.present
  · rw [ha] at ht0
    have hrun := RecoveryGatedSequence.reject_run streamMachine checkMachine 28
      (RecoveryRawLiteralStream.cost x.stream) _ first hr0 hh0 ht0
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have hl : RecoveryRawLiteralStream.cost x.stream+1 ≤ cost x := by unfold cost; omega
    have hm := runFrom_moreFuel machine (RecoveryRawLiteralStream.cost x.stream+1)
      (cost x-(RecoveryRawLiteralStream.cost x.stream+1)) _ r hr
    rw [Nat.add_sub_of_le hl] at hm
    have ho : output x=decoded x := by simp only [output,ha,Bool.false_eq_true,ite_false]
    refine ⟨r,hm,?_,hb.trans hl⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf0,ho]; rfl
    · rw [hf,hf0,ho]; rfl
  · have hy := decoded_valid x hx
    have hfield := decoded_field x ha
    have hcap : 2*(decoded x).bound.length+3 ≤ (decoded x).stream.data.data.capacity := by
      rw [hy.2]
      exact decoded_capacity x ha
    obtain ⟨last,hr1,hf1,_⟩ := check_run (decoded x) (indexWord x) hfield.1
      (hy.2.trans hfield.2.symm) hcap
    have he : RecoveryCalls.restarted checkMachine first.final.heads first.final.tapes=
        (decoded x).cfg checkMachine.start := by rw [hf0]; rfl
    rw [←he] at hr1
    rw [ha] at ht0
    have hrun := RecoveryGatedSequence.accept_run streamMachine checkMachine 28
      (RecoveryRawLiteralStream.cost x.stream) (4*x.bound.length+8+1+1) _ first last hr0 hh0 ht0 hr1
    obtain ⟨r,hr,hb,hf⟩ := hrun
    have ho : output x=marked (compared (decoded x) (indexWord x)) := by simp only [output,ha,ite_true]
    refine ⟨r,hr,?_,hb⟩
    apply configuration_ext
    · rfl
    · rw [hf,hf1,ho]; rfl
    · rw [hf,hf1,ho]; rfl

theorem output_stream (x : State) : (output x).stream=RecoveryRawLiteralStream.output x.stream := by
  unfold output
  split <;> rfl

theorem output_bound (x : State) : (output x).bound=x.bound := by
  unfold output
  split <;> rfl

theorem output_valid (x : State) (hx : x.Valid) : (output x).Valid := by
  have hy := decoded_valid x hx
  unfold output
  split <;> exact hy

theorem cost_bound (x : State) (hx : x.Valid) : cost x ≤ 2097152*(x.stream.width+1)^2 := by
  have hs := RecoveryRawLiteralStream.cost_bound x.stream
  unfold cost
  rw [hx.2]
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
