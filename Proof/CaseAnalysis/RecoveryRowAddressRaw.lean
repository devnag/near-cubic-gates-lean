import Proof.CaseAnalysis.RecoveryRowSources

/-! Remove framing from one actual projected-address batch using the
existing field copier and its physical finite count driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization GeneratedAmplifier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RepeatMachine.machine Copy.machine (fun _ _=>true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool)
    (total driver : ℕ):=RepeatMachine.cfg phase (Copy.cfg 0 source pos out) total driver

theorem remaining (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool)
    (total pos : ℕ) (hn : pos+fields.length=total) :
    Timed machine ((FieldList.stream fields).length+2*fields.length+total+3)
      (cfg 0 (pre++FieldList.stream fields++suffix) pre.length out total (pos+1))
      (cfg 3 (pre++FieldList.stream fields++suffix) (pre.length+(FieldList.stream fields).length)
        (out++fields.flatten) total 1) := by
  induction fields generalizing pre out pos with
  | nil=>
    have hp : pos=total:=by simpa only [List.length_nil,Nat.add_zero] using hn
    subst pos
    simpa only [machine,cfg,FieldList.stream_nil,List.flatten_nil,List.append_nil,List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
      using RepeatMachine.exhaust Copy.machine (fun _ _=>true) (Copy.cfg 0 (pre++suffix) pre.length out) total
  | cons bits fields ih=>
    obtain ⟨r,rr,rf,rs⟩:=Copy.copy_run pre bits (FieldList.stream fields++suffix) out
    have step:=RepeatMachine.iteration Copy.machine (fun _ _=>true)
      (Copy.cfg 0 (pre++frame bits++(FieldList.stream fields++suffix)) pre.length out)
      total pos r rfl (by simp only [List.length_cons] at hn;omega) rr
    rw [rf,rs] at step
    have tail:=ih (pre++frame bits) (out++bits) (pos+1) (by simp only [List.length_cons] at hn;omega)
    have hsource : (pre++frame bits)++FieldList.stream fields++suffix=
        pre++frame bits++(FieldList.stream fields++suffix) := by simp only [List.append_assoc]
    have hlen : (frame bits).length=2*bits.length+1:=frame_length bits
    have hmid : cfg 0 (pre++frame bits++(FieldList.stream fields++suffix))
        (pre.length+2*bits.length+1) (out++bits) total (pos+2)=
      cfg 0 ((pre++frame bits)++FieldList.stream fields++suffix)
        (pre++frame bits).length (out++bits) total ((pos+1)+1) := by
      rw [hsource,List.length_append,hlen]
      simp only [Nat.add_assoc]
    change Timed machine ((2*bits.length+1)+2)
      (cfg 0 (pre++frame bits++(FieldList.stream fields++suffix)) pre.length out total (pos+1))
      (cfg 0 (pre++frame bits++(FieldList.stream fields++suffix))
        (pre.length+2*bits.length+1) (out++bits) total (pos+2)) at step
    rw [hmid] at step
    have full:=step.trans tail
    have htime : 2*bits.length+1+2+((FieldList.stream fields).length+2*fields.length+total+3)=
        (FieldList.stream (bits::fields)).length+2*(bits::fields).length+total+3 := by
      simp only [FieldList.stream_cons,List.length_append,hlen,List.length_cons]
      omega
    rw [htime] at full
    simpa only [FieldList.stream_cons,List.flatten_cons,List.append_assoc,List.length_append,hlen,Nat.add_assoc] using full

def budget (fields : List (List Bool)):=(FieldList.stream fields).length+3*fields.length+3
theorem copy_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool) :
    ∃ r,runFrom machine (budget fields)
      (cfg 0 (pre++FieldList.stream fields++suffix) pre.length out fields.length 1)=some r ∧
      r.final=cfg 3 (pre++FieldList.stream fields++suffix) (pre.length+(FieldList.stream fields).length)
        (out++fields.flatten) fields.length 1 ∧ r.steps=budget fields := by
  have h:=remaining pre fields suffix out fields.length 0 (by omega)
  have he : (FieldList.stream fields).length+2*fields.length+fields.length+3=budget fields := by unfold budget;omega
  rw [he] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowAddress
