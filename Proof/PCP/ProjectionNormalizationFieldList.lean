import Proof.PCP.ProjectionNormalizationField

/-! Physical copying of a counted sequence of source fields. The literal
sentinel driver is consumed and rewound once; neither stream is rewound. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.FieldList
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stream (fields : List (List Bool)) : List Bool := (fields.map frame).flatten
noncomputable def machine := RepeatMachine.machine Field.machine (fun _ _ => true)
noncomputable def cfg (phase : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool)
    (total driver : ℕ) := RepeatMachine.cfg phase (Field.cfg 0 source pos out) total driver

@[simp] theorem stream_nil : stream []=[] := rfl
@[simp] theorem stream_cons (bits : List Bool) (fields : List (List Bool)) :
    stream (bits::fields)=frame bits++stream fields := rfl

theorem remaining (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool)
    (total pos : ℕ) (hn : pos+fields.length=total) :
    Timed machine ((stream fields).length+2*fields.length+total+3)
      (cfg 0 (pre++stream fields++suffix) pre.length out total (pos+1))
      (cfg 3 (pre++stream fields++suffix) (pre.length+(stream fields).length)
        (out++stream fields) total 1) := by
  induction fields generalizing pre out pos with
  | nil =>
    have hp : pos=total := by simpa using hn
    subst pos
    simpa only [machine,cfg,stream_nil,List.append_nil,List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
      using RepeatMachine.exhaust Field.machine (fun _ _ => true)
        (Field.cfg 0 (pre++suffix) pre.length out) total
  | cons bits fields ih =>
    obtain ⟨r,hr,hf,hs⟩ := Field.copy_run pre bits (stream fields++suffix) out
    have hstep := RepeatMachine.iteration Field.machine (fun _ _ => true)
      (Field.cfg 0 (pre++frame bits++(stream fields++suffix)) pre.length out)
      total pos r (by rfl) (by simp only [List.length_cons] at hn; omega) hr
    rw [hf,hs] at hstep
    have htail := ih (pre++frame bits) (out++frame bits) (pos+1)
      (by simp only [List.length_cons] at hn; omega)
    have hsource : (pre++frame bits)++stream fields++suffix=
        pre++frame bits++(stream fields++suffix) := by simp only [List.append_assoc]
    have hlen : (frame bits).length=2*bits.length+1 := frame_length bits
    have hmid : cfg 0 (pre++frame bits++(stream fields++suffix))
        (pre.length+2*bits.length+1) (out++frame bits) total (pos+2)=
      cfg 0 ((pre++frame bits)++stream fields++suffix)
        (pre++frame bits).length (out++frame bits) total ((pos+1)+1) := by
      rw [hsource,List.length_append,hlen]
      simp only [Nat.add_assoc]
    change Timed machine ((2*bits.length+1)+2)
      (cfg 0 (pre++frame bits++(stream fields++suffix)) pre.length out total (pos+1))
      (cfg 0 (pre++frame bits++(stream fields++suffix))
        (pre.length+2*bits.length+1) (out++frame bits) total (pos+2)) at hstep
    rw [hmid] at hstep
    have hall := hstep.trans htail
    have htime : (2*bits.length+1+2)+((stream fields).length+2*fields.length+total+3)=
        (stream (bits::fields)).length+2*(bits::fields).length+total+3 := by
      simp only [stream_cons,List.length_append,hlen,List.length_cons]
      omega
    rw [htime] at hall
    simpa only [stream_cons,List.append_assoc,List.length_append,hlen,Nat.add_assoc] using hall

theorem copy_run (pre : List Bool) (fields : List (List Bool)) (suffix out : List Bool) :
    ∃ r,runFrom machine ((stream fields).length+3*fields.length+3)
      (cfg 0 (pre++stream fields++suffix) pre.length out fields.length 1)=some r ∧
      r.final=cfg 3 (pre++stream fields++suffix) (pre.length+(stream fields).length)
        (out++stream fields) fields.length 1 ∧
      r.steps=(stream fields).length+3*fields.length+3 := by
  have h := remaining pre fields suffix out fields.length 0 (by omega)
  have he : (stream fields).length+2*fields.length+fields.length+3=
      (stream fields).length+3*fields.length+3 := by omega
  rw [he] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,
    controlConfig,RepeatMachine.phaseCode])

end NearCubicWires.RepairSource.ProjectionNormalization.FieldList
